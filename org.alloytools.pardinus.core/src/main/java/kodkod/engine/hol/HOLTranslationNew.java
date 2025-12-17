package kodkod.engine.hol;

import static kodkod.engine.hol.Proc.foldPlus;
import static kodkod.engine.hol.Proc.map;

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

import kodkod.ast.Decl;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.Relation;
import kodkod.ast.UnaryExpression;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.engine.Evaluator;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FullNegationPropagator;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.hol.Proc.Func1;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;
import kodkod.util.collections.Pair;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.AnnotatedNode;

public abstract class HOLTranslationNew extends HOLTranslation {

    /**========================================================================
     * Class HOLTranslationNew.FOL
     * ======================================================================== */
    public static class FOL extends HOLTranslationNew {
        final Proc.FOL proc;
        final FOL prev;
        Translation folTr;

        public FOL(Proc.FOL proc, Options options, int depth) {
            super(proc.bounds(), options);
            this.proc = proc;
            this.prev = null;
            
            //TODO: pass annotated instead, so that it doesn't have to re-annotate again
            folTr = options.solver().incremental()
                        ? Translator.translateIncremental(proc.formula, bounds, options)
                        : Translator.translate(proc.formula, bounds, options);
        }

        private FOL(FOL prev, Translation trNext) {
            super(trNext.bounds(), trNext.options());
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
        public SATSolver cnf()                            { return folTr.cnf(); }

        @Override
        public HOLTranslation next(Formula formula, Bounds bnds) {
            if (folTr.options().solver().incremental()) {
                folTr = Translator.translateIncremental(formula, bnds, (Translation.Incremental) folTr);
                return this;
            } else {
                return HOLTranslator.translateHOL(formulaWithInc().and(formula), Proc.union(bounds(), bnds), options, null, null);
            }
        }

        @Override
        public HOLTranslationNew next() {
            Translator.translateNext(folTr);
            return this;
        }
    }

    /**========================================================================
     * Class HOLTranslationNew.Some4All
     * ======================================================================== */
    public static class Some4All extends HOLTranslationNew {
        public final Proc.Some4All proc;
        private HOLTranslation candTr;
        private int numCandidates;

        public Some4All(Proc.Some4All proc, Options options, int depth) {
            super(proc.bounds(), options, depth);
            this.proc = proc;
            Proc ffp = proc.fullFlippedProc();
            this.candTr = ffp.translate(options, depth + 1, null);
            this.numCandidates = -1;
        }

        public Formula formula()                          { return proc.formula(); }
        public HOLTranslation convTr()                    { return candTr; }
        public Translation getCurrentLTLTranslation()     { return candTr.getCurrentLTLTranslation(); }

        public HOLTranslation next()                      { candTr = candTr.next();  return this; }
        public HOLTranslation next(Formula f, Bounds b)   { candTr = candTr.next(f, b); return this; }

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
                int maxIter = options.getHolSome4AllMaxIter();
                while (candTr.cnf().solve()) {
                    iterCnt++;
                    Instance cand = candTr.interpret();
                    rep.holCandidateFound(Some4All.this, cand);

                    Formula checkFormula = Formula.and(proc.qpFormulas()).not();

                    
                    // verifying candidate
                    Bounds pi = bounds.clone();
                    for (Relation r : pi.relations()) {
                        pi.boundExactly(r, cand.tuples(r));
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
                        Instance cex = checkTr.interpret();
                        
                        rep.holCandidateNotVerified(Some4All.this, cand, cex);

                        Collection<Relation> holSkolems = cand.skolems();
                        holSkolems.removeAll(bounds.skolems());

                        List<Formula> cexInsts = new ArrayList<Formula>(proc.qpFormulas().length);
                        top: for (Formula f : proc.qpFormulas()) {
                                final Map<Variable, Expression> varmap = new HashMap<Variable, Expression>();
                                QuantifiedFormula qf = (QuantifiedFormula) f;
                                for (Decl d : qf.decls()) {
                                    Relation sk = findSkolemRelation(holSkolems, d.variable());
                                    TupleSet skTuples = cex.tuples(sk.name());
                                    if (skTuples == null) continue top; // the cex does not involve this qf, so skip to next
                                    varmap.put(d.variable(), pi.ts2expr(skTuples));
                                }
                                cexInsts.add(qf.formula().accept(new AbstractReplacer(new HashSet<Node>()) {
                                    @Override
                                    public Expression visit(Variable variable) {
                                        Expression expr = varmap.get(variable);
                                        if (expr == null) return super.visit(variable);
                                        if (expr == Expression.NONE)
                                            for (int i = 1; i < variable.arity(); i++)
                                                expr = expr.product(Expression.NONE);
                                        return expr;
                                    }
                                }));
                        }
                        Formula fInc = Formula.and(cexInsts);
                        Bounds bInc = new Bounds(candTr.bounds().universe());
                        Proc x;
                        if (!options.isHolFullIncrements()) {
                            Bounds bCand = candTr.bounds();
                            x = HOLTranslator.toProc(fInc, bCand, options);
                            Pair<Formula, Bounds> p = x.firstOrderProblem();
                            Set<Relation> diff = new HashSet<Relation>(p.b.relations());
                            diff.removeAll(bCand.relations());
                            bInc = new Bounds(bCand.universe());
                            for (Relation r: diff) {
                                bInc.bound(r, p.b.lowerBound(r), p.b.upperBound(r));
                            }
                            fInc = p.a;
                        } else {
                            fInc = FullNegationPropagator.toNNF(AnnotatedNode.annotateRoots(fInc)).node();
                        }

                        rep.holFindingNextCandidate(Some4All.this, fInc);
                        try {
                            candTr = candTr.next(fInc, bInc);
                        } catch (HigherOrderDeclException e) {
                            candTr = HOLTranslator.translateHOL(candTr.formulaWithInc().and(fInc), candTr.bounds(), options, null, Collections.EMPTY_MAP);
                        }
                    }
                }
                long end = System.currentTimeMillis() - start;

                numCandidates = iterCnt;
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
    }

    /**========================================================================
     * Class HOLTranslationNew.ORSplit
     * ======================================================================== */
    public static class OR extends HOLTranslationNew {
        public final Proc.OR proc;
        private final HOLTranslation[] splitTransl;
        private HOLTranslation solTr = null;
        private int currTrIdx = 0;

        public OR(final Proc.OR proc, final Options options, final int depth) {
            super(Proc.union(map(proc.disjuncts, new Bounds[0], new Func1<Proc, Bounds>() {
                public Bounds run(Proc a) { return a.bounds; }
            })), options, depth);
            this.proc = proc;
            this.splitTransl = map(proc.disjuncts, new HOLTranslation[0], new Func1<Proc, HOLTranslation>() {
                public HOLTranslation run(Proc a) { return a.translate(options, depth + 1, null); }
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
    }

    protected HOLTranslationNew(Bounds bounds, Options options)            { this(bounds, options, 0); }
    protected HOLTranslationNew(Bounds bounds, Options options, int depth) {
        super(bounds, options, depth);
    }
}
