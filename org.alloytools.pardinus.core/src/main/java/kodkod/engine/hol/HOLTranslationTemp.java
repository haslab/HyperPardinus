package kodkod.engine.hol;

import static kodkod.engine.hol.Proc.foldPlus;
import static kodkod.engine.hol.Proc.map;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collector;
import java.util.stream.Collectors;

import javax.management.RuntimeErrorException;

import kodkod.ast.Decl;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.Evaluator;
import kodkod.engine.Statistics;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FullNegationPropagator;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.hol.HOLTranslationTemp.OR;
import kodkod.engine.hol.Proc.Func1;
import kodkod.engine.ltl2fol.TemporalTranslation;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleSet;
import kodkod.util.collections.Pair;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.AnnotatedNode;

public abstract class HOLTranslationTemp extends HOLTranslation {
    
    protected abstract HOLTranslation next(Map<Formula,List<TemporalInstance>> cexs);

    /**========================================================================
     * Class HOLTranslationNew.FOL
     * ======================================================================== */
    public static class FOL extends HOLTranslationTemp {
        final Proc.FOL proc;
        final FOL prev;
        TemporalTranslation folTr;
        private TemporalInstance cand;
        private Map<Formula,List<TemporalInstance>> cexs;

        public FOL(Proc.FOL proc, ExtendedOptions options, int depth, TemporalInstance cand, Map<Formula,List<TemporalInstance>> cexs) {
            super((PardinusBounds) proc.bounds(), options);
            this.proc = proc;
            this.prev = null;
            this.cand = (TemporalInstance) cand;
            this.cexs = cexs;
            options.setMinTraceLength(Math.max(options.minTraceLength(),cand!=null?cand.prefixLength():0));
            folTr = TemporalTranslator.translate(proc.formula, (PardinusBounds) bounds(), options, this.cand, this.cexs);

            //TODO: pass annotated instead, so that it doesn't have to re-annotate again
//            folTr = options.solver().incremental()
//                        ? Translator.translateIncremental(proc.formula, bounds, options)
//                        : Translator.translate(proc.formula, bounds, options);
        }

        private FOL(FOL prev, TemporalTranslation trNext) {
            super((PardinusBounds) trNext.bounds(), trNext.options());
            this.proc = prev.proc;
            this.folTr = trNext;
            this.prev = prev;
        }

        public final boolean isFirstOrder()               { return true; }
        public Formula formula()                          { return proc.formula; }
        public Translation getCurrentLTLTranslation()     { return folTr; }

        public int numCandidates()                        { return 1; }
        public IntSet primaryVariables(Relation relation) { return folTr.primaryVariables(relation); }
        public int numPrimaryVariables()                  { return folTr.numPrimaryVariables(); }
        public SATSolver cnf()                            { return new Solver(); }
        public Instance interpret( ) { return interpret(proc.bounds); };
        public Instance interpret(Bounds bounds) {return new TemporalInstance(folTr.interpretStatic(), (PardinusBounds) bounds); };

        int aux = 0;
        
        class Solver implements SATSolver {

            @Override
            public int numberOfVariables() {
                return folTr.cnf().numberOfVariables();
            }

            @Override
            public int numberOfClauses() {
                return folTr.cnf().numberOfClauses();
            }

            @Override
            public void addVariables(int numVars) {
                folTr.cnf().addVariables(numVars);
            }

            @Override
            public boolean addClause(int[] lits) {
                return folTr.cnf().addClause(lits);
            }

            @Override
            public boolean solve() throws SATAbortedException {
                SATSolver cnf = folTr.cnf();

                options.reporter().solvingCNF(folTr.traceLength(), folTr.numPrimaryVariables(), cnf.numberOfVariables(),
                        cnf.numberOfClauses());
                long start = System.currentTimeMillis();
                boolean isSat = cnf.solve();
                aux += System.currentTimeMillis() - start;

                while (!isSat && folTr.traceLength() < ((ExtendedOptions) options).maxTraceLength()) {
                    start = System.currentTimeMillis();
                    folTr = TemporalTranslator.nextStep(folTr);
                    long end = System.currentTimeMillis() - start;

                    cnf = folTr.cnf();
                   
                    options.reporter().solvingCNF(folTr.traceLength(), folTr.numPrimaryVariables(), cnf.numberOfVariables(),
                            cnf.numberOfClauses());
                    start = System.currentTimeMillis();
                    isSat = cnf.solve();
                    aux += System.currentTimeMillis() - start;
                }
                return isSat;
            }

            @Override
            public boolean valueOf(int variable) {
                return folTr.cnf().valueOf(variable);
            }

            @Override
            public void free() {
                folTr.cnf().free();
            }

        }
        
        @Override
        public HOLTranslation next(Formula formula, Bounds bnds) {
//            if (folTr.options().solver().incremental()) {
//                folTr = Translator.translateIncremental(formula, bnds, (Translation.Incremental) folTr);
//                return this;
//            } else {
                ((ExtendedOptions) options).setMinTraceLength(folTr.traceLength());
                return HOLTranslator.translateHOL(formulaWithInc().and(formula), Proc.union(bounds(), bnds), options, null, null);
//            }
        }

        @Override
        public HOLTranslationTemp next() {
        	TemporalInstance ti = (TemporalInstance) interpret();
			TemporalTranslator.remove(folTr,ti,0,-1,new HashSet<Relation>(),folTr.bounds().relations());
        	folTr = TemporalTranslator.translateNext(folTr);
            return this;
        }

        @Override
        protected HOLTranslation next(Map<Formula,List<TemporalInstance>> cexs) {
            if (folTr.options().solver().incremental()) {
            	TemporalInstance ti = (TemporalInstance) interpret();
    			TemporalTranslator.remove(folTr,ti,0,-1,new HashSet<Relation>(),folTr.bounds().relations());
//            	folTr = TemporalTranslator.translateNext(folTr);
            	
            	int maxlen = 0;
            	maxlen = cexs.values().stream().flatMap(x -> x.stream()).mapToInt(x -> x.prefixLength()).max().getAsInt();

            	while (maxlen > folTr.traceLength())
                    folTr = TemporalTranslator.nextStep(folTr); // inefficient, set to maxlen

                folTr = TemporalTranslator.translateIncremental(folTr,cexs);
                return this;
            } else {
                ((ExtendedOptions) options).setMinTraceLength(folTr.traceLength());
                for (Formula f : this.cexs.keySet())
                    cexs.merge(f, this.cexs.get(f), (v1, v2) -> {
                        v1.addAll(v2);
                        return v1;
                    });
                return HOLTranslator.translateHOL(formulaWithInc(), bounds(), options, this.cand, cexs);
            }
        }
    }

    /**========================================================================
     * Class HOLTranslationNew.Some4All
     * ======================================================================== */
    public static class Some4All extends HOLTranslationTemp {
        public final Proc.Some4All proc;
        private HOLTranslationTemp candTr;
        private int numCandidates;

        public Some4All(Proc.Some4All proc, Options options, int depth, Instance cand) {
            super((PardinusBounds) proc.bounds(), options, depth);
            this.proc = proc;
            Proc ffp = proc.fullFlippedProc();
            this.candTr = (HOLTranslationTemp) ffp.translate(options, depth + 1, cand);
            this.numCandidates = -1;
        }

        public Formula formula()                          { return proc.formula(); }
        public HOLTranslation convTr()                    { return candTr; }
        public Translation getCurrentLTLTranslation()     { return candTr.getCurrentLTLTranslation(); }

        public HOLTranslation next()                      { candTr = (HOLTranslationTemp) candTr.next();  return this; }
        public HOLTranslation next(Formula f, Bounds b)   { candTr = (HOLTranslationTemp) candTr.next(f, b); return this; }

        public int numCandidates()                        { return numCandidates; }

        // Translation methods -----------

        public IntSet primaryVariables(Relation relation) { return candTr.primaryVariables(relation); }
        public int numPrimaryVariables()                  { return candTr.numPrimaryVariables(); }
        public SATSolver cnf()                            { return new Solver(); }
        public Instance interpret()                       { return candTr.interpret(bounds); }

        // Replacer ----------------------

        class Replacer extends AbstractReplacer {
            protected Replacer(Set<Node> cached) {
                super(cached);
            }
        }

        // SATSolver methods -------------

        class Solver implements SATSolver {
            public int numberOfVariables()        { return candTr.cnf().numberOfVariables(); }
            public int numberOfClauses()          { return candTr.cnf().numberOfClauses(); }
            public void addVariables(int numVars) { candTr.cnf().addVariables(numVars); }
            public boolean addClause(int[] lits)  { return candTr.cnf().addClause(lits); }
            public boolean valueOf(int variable)  { return candTr.cnf().valueOf(variable); }
            public void free()                    { candTr.cnf().free(); }
            public boolean solveNext()            {
                long start = System.currentTimeMillis();

                // finding the next candidate
                int iterCnt = 0;
                int maxIter = 500000;//options.getHolSome4AllMaxIter();
                while (candTr.cnf().solve()) {
                    iterCnt++;
                    TemporalInstance cand = ((TemporalInstance) candTr.interpret());
                    Set<Relation> rems = new HashSet<Relation>();
                    for (Relation r: cand.state(0).relations()) {
                    	if (!bounds.relations().contains(r))
                    		rems.add(r);
                    }
                    for (Relation r: rems)
                    	cand.remove(r);
                    cand = cand.canonize();
                                 	 
                    
                    rep.holCandidateFound(Some4All.this, cand);

                    Formula checkFormula = Formula.and(proc.qpFormulas()).not();

                    // verifying candidate
                    Bounds pi = bounds.clone();
                    for (Relation r : pi.relations()) {
                        TupleSet ts = pi.universe().factory().noneOf(r.arity());
                        for (int i = 0; i < cand.prefixLength(); i++)
                            ts.addAll(cand.state(i).tuples(r));
                        pi.boundExactly(r, ts);
                    }

                    rep.holVerifyingCandidate(Some4All.this, cand, checkFormula, pi);
                    Options opt = options.clone();
                    
                    //opt.setOverflowPolicy(opt.overflowPolicy().dual);
                    HOLTranslation checkTr = HOLTranslator.translateHOL(checkFormula, pi, opt, cand, Collections.EMPTY_MAP);
                    if (!checkTr.cnf().solve()) {
                        numCandidates = iterCnt;
                        rep.holCandidateVerified(Some4All.this, cand);
                        return true;
                    } else {
                        if (maxIter > 0 && iterCnt > maxIter) throw new HOLException("[Some4All] Max number of iterations reached: " + maxIter);
                        TemporalInstance cex = (TemporalInstance) checkTr.interpret();
                        rep.holCandidateNotVerified(Some4All.this, cand, cex);

                        Map<Formula,List<TemporalInstance>> cexs = new HashMap<>();
                        for (Formula f : proc.qpFormulas()) {
                            cexs.putIfAbsent(f, new ArrayList());
                            cexs.get(f).add(cex);
                        }

                        rep.holFindingNextCandidate(Some4All.this, cex);
                        try {
                            candTr = (HOLTranslationTemp) candTr.next(cexs);
                        } catch (HigherOrderDeclException e) {
                            candTr = (HOLTranslationTemp) HOLTranslator.translateHOL(candTr.formulaWithInc(), candTr.bounds(), options, cand, cexs);
                        }
                    }
                }
                long end = System.currentTimeMillis() - start; // 217511

                numCandidates = iterCnt; // 20556
                return false;
            }
            public boolean solve() throws SATAbortedException {
                rep.holLoopStart(Some4All.this, candTr.formula(), candTr.bounds());
                return solveNext();
            }
        }

        public Relation findSkolemRelation(Collection<Relation> holSkolems, Variable variable) {
            for (Relation r: holSkolems)
                if (r.getSkolemVar() == variable)
                    return r;
            assert false : "Skolem relation not found for variable " + variable;
            return null;
        }

        @Override
        protected HOLTranslation next(Map<Formula,List<TemporalInstance>> cexs) {
            // TODO Auto-generated method stub
            return null;
        }
    }

    /**========================================================================
     * Class HOLTranslationNew.ORSplit
     * ======================================================================== */
    public static class OR extends HOLTranslationTemp {
        public final Proc.OR proc;
        private final HOLTranslation[] splitTransl;
        private HOLTranslation solTr = null;
        private int currTrIdx = 0;

        public OR(final Proc.OR proc, final Options options, final int depth, Instance cand) {
            super((PardinusBounds) Proc.union(map(proc.disjuncts, new Bounds[0], new Func1<Proc, Bounds>() {
                public Bounds run(Proc a) { return a.bounds; }
            })), options, depth);
            this.proc = proc;
            this.splitTransl = map(proc.disjuncts, new HOLTranslation[0], new Func1<Proc, HOLTranslation>() {
                public HOLTranslation run(Proc a) { return a.translate(options, depth + 1, cand); }
            });
        }

        public HOLTranslation currTr()                    { return splitTransl[currTrIdx]; }
        public Formula formula()                          { return proc.formula(); }
        public Translation getCurrentLTLTranslation()     { return currTr().getCurrentLTLTranslation(); }

        public HOLTranslation next()                      { splitTransl[currTrIdx] = currTr().next();  return this; }
        public HOLTranslation next(Formula f)             { splitTransl[currTrIdx] = currTr().next(f); return this; }
        public HOLTranslation next(Formula f, Bounds b)   { splitTransl[currTrIdx] = currTr().next(f, b); return this; }

        public int numCandidates()                        { return currTrIdx; }

        // Translation methods -----------

        public IntSet primaryVariables(Relation relation) { return splitTransl[0].primaryVariables(relation); } //TODO enough?
        public int numPrimaryVariables()                  { return foldPlus(splitTransl, new Func1<HOLTranslation, Integer>() { public Integer run(HOLTranslation a) { return a.numPrimaryVariables(); }}); }
        public SATSolver cnf()                            { return new Solver(); }
        public Instance interpret()                       { assert solTr != null : "no solution was found"; return solTr.interpret(); }
        public Instance interpret(Bounds bnds)            { assert solTr != null : "no solution was found"; return solTr.interpret(bnds); }

        // SATSolver methods -------------


        class Solver implements SATSolver {
            public int numberOfVariables()        { return currTr().cnf().numberOfVariables(); }
            public int numberOfClauses()          { return currTr().cnf().numberOfClauses(); }
            public void addVariables(int numVars) { currTr().cnf().addVariables(numVars); }
            public boolean addClause(int[] lits)  { return currTr().cnf().addClause(lits); }
            public boolean valueOf(int variable)  { return currTr().cnf().valueOf(variable); }
            public void free()                    { currTr().cnf().free(); }
            public boolean solveNext() throws SATAbortedException {
                for (int i = currTrIdx; i < splitTransl.length; i++) {
                    currTrIdx = i;
                    HOLTranslation tr = currTr();
                    rep.holSplitChoice(OR.this, tr.formula(), tr.bounds());
                    if (tr.cnf().solve()) {
                        solTr = tr;
                        rep.holSplitChoiceSAT(OR.this, solTr.interpret());
                        return true;
                    } else {
                    	rep.holSplitChoiceUNSAT(OR.this);
                    };
                }
                solTr = null;
                return false;
            }
            public boolean solve() throws SATAbortedException {
                rep.holSplitStart(OR.this, formula());
                currTrIdx = 0;
                return solveNext();
            }
        }

        @Override
        protected HOLTranslation next(Map<Formula,List<TemporalInstance>> cexs) {
        	splitTransl[currTrIdx] = ((HOLTranslationTemp) currTr()).next(cexs); return this;
        }
    }

    protected HOLTranslationTemp(PardinusBounds bounds, Options options)            { this(bounds, options, 0); }
    protected HOLTranslationTemp(PardinusBounds bounds, Options options, int depth) {
        super(bounds, options, depth);
    }
}
