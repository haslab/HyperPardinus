/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2013-present, Nuno Macedo, INESC TEC
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.ltl2fol;

import kodkod.ast.*;
import kodkod.ast.RelationPredicate.Function;
import kodkod.ast.operator.FormulaOperator;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.FullNegationPropagator;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.hol.HOLTranslator;
import kodkod.engine.hol.Proc;
import kodkod.engine.hol.TemporalHOLTranslation;
import kodkod.instance.*;
import kodkod.util.collections.Pair;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.AnnotatedNode;

import java.util.*;

/**
 * Expands temporal problems into plain problems, i.e., formulas with
 * {@link kodkod.ast.operator.TemporalOperator temporal operators} and bounds
 * over {@link kodkod.ast.VarRelation variable relations}, into regular Kodkod
 * static problems, i.e., standard {@link kodkod.ast.Formula formulas} and
 * {@link kodkod.instance.Bounds bounds}, following the provided
 * {@link kodkod.engine.config.TemporalOptions temporal options}.
 *
 * Relations are introduced to explicitly model the (bounded) temporal trace,
 * and variable relations are expanded to static ones that refer to that trace.
 * To provide sound loop bounded model checking semantics for past operators,
 * loops are unrolled according to the past operator depth.
 *
 * As of Pardinus 1.1, traces are assumed to always loop.
 *
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] temporal model finding
 */
public class TemporalTranslator {

	/** The name assigned to {@link #STATE state} atoms. */
	public static final String STATEATOM = "Time";

	/** Relations representing the explicit trace of the temporal problem. **/
	public static final Relation STATE = Relation.unary(STATEATOM);
	public static final Relation FIRST = Relation.unary("S/first");
	public static final Relation LAST = Relation.unary("S/last");
	public static final Relation PREFIX = Relation.binary("S/next");
	public static final Relation LOOP = Relation.unary("loop");
	public static final Expression TRACE = PREFIX.union(LAST.product(LOOP));

	public static final Relation LAST_ = Relation.unary("S/last_"); 			// ExplicitUnrolls = true
	public static final Relation UNROLL_MAP = Relation.binary("unroll_map"); 	// ExplicitUnrolls = true

	public static final Relation LEVEL = Relation.unary("Level"); 				// ExplicitUnrolls = false
	public static final Relation L_FIRST = Relation.unary("L/first"); 			// ExplicitUnrolls = false
	public static final Relation L_LAST = Relation.unary("L/last"); 			// ExplicitUnrolls = false
	public static final Relation L_PREFIX = Relation.binary("L/next"); 			// ExplicitUnrolls = false

	public static final String STATE_SEP = "_";

	public static final Expression START = L_FIRST.product(FIRST).union(L_FIRST.join(L_PREFIX.closure()).product(LOOP));

	/** The original temporal formula. */
	private final Formula formula;
	/** The original variable bounds. */
	private final PardinusBounds bounds;
	/** The past operator depth. */
	private final int past_depth;
	/** Map logging the translation of temporal formulas, from resulting formula to original one. **/
	private final Map<Formula,Formula> tempTransLog = new HashMap<Formula,Formula>();
	
	
	/**
	 * Constructs a new temporal translator to expand temporal formulas and variable
	 * bounds.
	 * 
	 * @param form
	 *            the original temporal formula.
	 * @param bnds
	 *            the original variable bounds.
	 */
	private TemporalTranslator(Formula formula, PardinusBounds bounds, Options options) {
	    bounds = bounds.clone();

		// [HASLab] if not decomposed, use the amalgamated if any
		if (!options.decomposed() && bounds.amalgamated!=null)
			bounds = bounds.amalgamated();
		
		// [HASLab] retrieve the additional formula imposed by the symbolic
		// bounds, depending on execution stage
		Formula symbForm = Formula.TRUE;
		// [HASLab] if decomposed mode, the amalgamated bounds are always considered
		if (options.decomposed() && bounds.amalgamated() != null)
			symbForm = bounds.amalgamated().resolve(options.reporter());
		// [HASLab] then use regular bounds
		symbForm = symbForm.and(bounds.resolve(options.reporter()));

		formula = formula.and(symbForm);
		this.formula = formula;
		this.bounds = bounds;
		this.past_depth = countHeight(formula);
	}

	/**
	 * Translates {@link PardinusBounds temporal bound} into standard bounds by
	 * expanding the bound trace over {@link kodkod.ast.VarRelation variable
	 * relations} by appending the {@link #STATE state sig} to the bound. The bounds
	 * of static relations should remain unchanged. The size of the bounds depends
	 * on the trace length passed. Unrolls must be applied if there are past
	 * operators. If the formula contains "always" operator, the bounds can be
	 * optimized.
	 * 
	 * @see TemporalBoundsExpander
	 * 
	 * @param traceLength
	 *            the current trace length.
	 * @return the temporal bounds expanded into standard bounds.
	 */
	private PardinusBounds expand(int traceLength) {
		return TemporalBoundsExpander.expand(bounds, traceLength, past_depth);
	}

	private PardinusBounds  expand(int traceLength, TemporalInstance cand) {
		return TemporalBoundsExpander.expand(bounds, traceLength, past_depth, cand);
	}

	/**
	 * Converts an LTL temporal formula into its FOL static representation. The
	 * formula is previously converted into negative normal form (NNF) to guarantee
	 * the correct translation of the temporal operators. The
	 * {@link kodkod.ast.VarRelation variable relations} contain themselves their
	 * representation into the expanded static shape. If there are no past operators
	 * or there are "always" operators, the translation can be simplified.
	 * 
	 * @see LTL2FOLTranslator
	 * 
	 * @return the static version of the temporal formula.
	 */
	private Formula translate() {
		tempTransLog.clear();
		return LTL2FOLTranslator.translate(formula, 0, past_depth > 1, tempTransLog);
	}

	/**
	 * Checks whether an AST node has temporal constructs, i.e., occurrences of
	 * {@link kodkod.ast.operator.TemporalOperator temporal operations} or
	 * {@link kodkod.ast.VarRelation variable relations}.
	 * 
	 * @param node
	 *            the node to be checked.
	 * @return whether the node has temporal constructs.
	 */
	public static boolean isTemporal(Node node) {
		AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
			@Override
			public Boolean visit(UnaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(BinaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(TempExpression tempExpr) {
				return cache(tempExpr, true);
			}

			@Override
			public Boolean visit(Relation relation) {
				return cache(relation, relation.isVariable());
			}
		};
		return (boolean) node.accept(det);
	}
	
	public static boolean hasTemporalOps(Node node) {
		AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
			@Override
			public Boolean visit(UnaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(BinaryTempFormula tempFormula) {
				return cache(tempFormula, true);
			}

			@Override
			public Boolean visit(TempExpression tempExpr) {
				return cache(tempExpr, true);
			}
			
		};
		return (boolean) node.accept(det);
	}

	/** Count the depth of past operators of the given AST tree. */
	public static int countHeight(Node node) {
		ReturnVisitor<Integer, Integer, Integer, Integer> vis = new ReturnVisitor<Integer, Integer, Integer, Integer>() {
			private int max(int a, int b) {
				return (a >= b) ? a : b;
			}

			private int max(int a, int b, int c) {
				return (a >= b) ? (a >= c ? a : c) : (b >= c ? b : c);
			}

			public Integer visit(Relation x) {
				return 0;
			}

			public Integer visit(IntConstant x) {
				return 0;
			}

			public Integer visit(ConstantFormula x) {
				return 0;
			}

			public Integer visit(Variable x) {
				return 0;
			}

			public Integer visit(ConstantExpression x) {
				return 0;
			}

			public Integer visit(NotFormula x) {
				return x.formula().accept(this);
			}

			public Integer visit(UnaryTempFormula x) {
				int n = 0;
				if (x.op().equals(TemporalOperator.ONCE) || x.op().equals(TemporalOperator.HISTORICALLY)
						|| x.op().equals(TemporalOperator.BEFORE))
					n = 1;
				int l = x.formula().accept(this);
				return n + l;
			} // [HASLab] temporal nodes

			public Integer visit(IntToExprCast x) {
				return x.intExpr().accept(this);
			}

			public Integer visit(Decl x) {
				return x.expression().accept(this);
			}

			public Integer visit(ExprToIntCast x) {
				return x.expression().accept(this);
			}

			public Integer visit(UnaryExpression x) {
				return x.expression().accept(this);
			}

			public Integer visit(TempExpression x) {
				return x.expression().accept(this);
			} // [HASLab] temporal nodes

			public Integer visit(UnaryIntExpression x) {
				return x.intExpr().accept(this);
			}

			public Integer visit(MultiplicityFormula x) {
				return x.expression().accept(this);
			}

			public Integer visit(BinaryExpression x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(ComparisonFormula x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(BinaryFormula x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(BinaryTempFormula x) {
				int n = 0;
				if (x.op().equals(TemporalOperator.SINCE) || x.op().equals(TemporalOperator.TRIGGERED))
					n = 1;
				int l = max(x.left().accept(this), x.right().accept(this));
				return n + l;
			} // [HASLab] temporal nodes

			public Integer visit(BinaryIntExpression x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(IntComparisonFormula x) {
				return max(x.left().accept(this), x.right().accept(this));
			}

			public Integer visit(IfExpression x) {
				return max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this));
			}

			public Integer visit(IfIntExpression x) {
				return max(x.condition().accept(this), x.thenExpr().accept(this), x.elseExpr().accept(this));
			}

			public Integer visit(SumExpression x) {
				return max(x.decls().accept(this), x.intExpr().accept(this));
			}

			public Integer visit(QuantifiedFormula x) {
				return max(x.decls().accept(this), x.formula().accept(this));
			}

			public Integer visit(Comprehension x) {
				return max(x.decls().accept(this), x.formula().accept(this));
			}

			public Integer visit(Decls x) {
				int max = 0, n = x.size();
				for (int i = 0; i < n; i++)
					max = max(max, x.get(i).accept(this));
				return max;
			}

			public Integer visit(ProjectExpression x) {
				int max = x.expression().accept(this);
				for (Iterator<IntExpression> t = x.columns(); t.hasNext();) {
					max = max(max, t.next().accept(this));
				}
				return max;
			}

			public Integer visit(RelationPredicate x) {
				if (x instanceof Function) {
					Function f = ((Function) x);
					return max(f.domain().accept(this), f.range().accept(this));
				}
				return 0;
			}

			public Integer visit(NaryExpression x) {
				int max = 0;
				for (int m = 0, n = x.size(), i = 0; i < n; i++) {
					m = x.child(i).accept(this);
					if (i == 0 || max < m)
						max = m;
				}
				return max;
			}

			public Integer visit(NaryIntExpression x) {
				int max = 0;
				for (int m = 0, n = x.size(), i = 0; i < n; i++) {
					m = x.child(i).accept(this);
					if (i == 0 || max < m)
						max = m;
				}
				return max;
			}

			public Integer visit(NaryFormula x) {
				int max = 0;
				for (int m = 0, n = x.size(), i = 0; i < n; i++) {
					m = x.child(i).accept(this);
					if (i == 0 || max < m)
						max = m;
				}
				return max;
			}

		};
		Object ans = node.accept(vis);
		if (ans instanceof Integer)
			return ((Integer) ans).intValue() + 1;
		else
			return 1;
	}

//	/** Tests whether an always operator occurs in the given AST tree. */
//	private static boolean hasAlways(Node node) {
//		final AbstractDetector detector = new AbstractDetector(Collections.emptySet()) {
//			public Boolean visit(UnaryTempFormula form) {
//				if (form.op() == TemporalOperator.ALWAYS)
//					return cache(form, Boolean.TRUE);
//				return super.visit(form);
//			}
//		};
//		return (Boolean) node.accept(detector);
//	}
	
	/** Interprets the step of a state tuple from its name. */
	public static int interpretState(Tuple tuple) {
		String label = tuple.atom(0).toString();
		String[] labelS = label.split(STATE_SEP);
		return Integer.valueOf(labelS[0].substring(4)); 
	}

	/** Interprets the unrolled step of a state tuple from its name. */
	public static int interpretUnroll(Tuple tuple) {
		String label = tuple.atom(0).toString();
		String[] labelS = label.split(STATE_SEP);
		return Integer.valueOf(labelS[1])+1; 
	}

	public static TemporalTranslation translate(Formula formula, PardinusBounds bounds, ExtendedOptions options) {
		return translate(formula,bounds,options,null,new HashMap<>());
	}

	public static TemporalTranslation translate(Formula formula, PardinusBounds bounds, ExtendedOptions options, TemporalInstance cand) {
		return translate(formula,bounds,options,cand,new HashMap<>());
	}

	public static TemporalTranslation translateIncremental(TemporalTranslation tmptrans, Map<Formula, List<TemporalInstance>> adds) {
		List<Formula> news = new ArrayList<>();
		for (Formula f : adds.keySet()) {
			for (TemporalInstance i : adds.get(f)) {
				if (i.prefixLength() <= tmptrans.traceLength()) {
					Formula nw = extendFormulas(f,i,tmptrans.extBounds(),tmptrans.bounds(),tmptrans.options());
					news.add(nw);
				} else {
					System.out.println("Ignoring %d because at %d.".formatted(i.prefixLength(),tmptrans.traceLength()));
				}
			}
		}

		Bounds new_ext = new PardinusBounds(tmptrans.extBounds().universe());
		for (Relation r: tmptrans.extBounds().relations()) {
			if (!tmptrans.translation.bounds().relations().contains(r))
				new_ext.bound(r, tmptrans.extBounds().lowerBound(r), tmptrans.extBounds().upperBound(r));
		}
		Translation.Incremental translation = Translator.translateIncremental(Formula.compose(FormulaOperator.AND,news), new_ext , (Translation.Incremental) tmptrans.translation);

		for (Formula f: tmptrans.adds.keySet())
			adds.merge(f, tmptrans.adds.get(f), (v1,v2) -> { v1.addAll(v2); return v1; });

		TemporalTranslation ntmp = new TemporalTranslation(translation,tmptrans.traceLength(),tmptrans.pastDepth(),tmptrans.extFormula().and(Formula.compose(FormulaOperator.AND,news)),tmptrans.extBounds(),tmptrans.formula(),tmptrans.bounds(),tmptrans.options(),tmptrans.cand,adds);
		ntmp.addSeenSol(tmptrans.seenSols());
		return ntmp; 

	}

	private static final Map<Formula, Formula> cache = new HashMap<Formula,Formula>();

	public static TemporalTranslation translate(Formula formula, PardinusBounds bounds, ExtendedOptions options, TemporalInstance cand, Map<Formula, List<TemporalInstance>> adds) {
		TemporalTranslator tmptrans = new TemporalTranslator(formula, bounds, options);
		Formula extformula = tmptrans.translate();

		Translation translation = null;
		int traceLength = options.minTraceLength()-1;
		PardinusBounds extbounds = null;
		// increase while UNSAT and below max
		do {
			traceLength++;
			extbounds = tmptrans.expand(traceLength,cand);
			extbounds.ensureAtomRelations();
			// needed for HOL
//            Map<String,TemporalInstance> cache = new HashMap();
			for (Formula f : adds.keySet())
				for (TemporalInstance i : adds.get(f)) {
//                    Formula xx = Formula.FALSE;
//                    for (TemporalInstance j : i.unrollStep(traceLength,tmptrans.past_depth)) {
//                        xx = xx.or(LOOP.eq(extbounds.ensureAtomExpr(j.tuples(LOOP).iterator().next().atom(0))).not());
//                        i = j;
//                    }
					i = i.unrollStep(traceLength,tmptrans.past_depth).iterator().next();
					extformula = extformula.and(extendFormulas(f,i,extbounds,bounds,options));
				}
			translation = Translator.translateIncremental(extformula, extbounds, options);
//            if (options.logTranslation() > 0)
//                translation.log().logTempTranslation(tmptrans.tempTransLog);
		} while (translation.trivial() && traceLength < options.maxTraceLength());
		return new TemporalTranslation(translation,traceLength,tmptrans.past_depth,extformula,extbounds,formula,bounds,options,cand,adds);
	}
	
	public static TemporalHOLTranslation translate2proc(Formula formula, PardinusBounds bounds, ExtendedOptions options, int k) {
		TemporalTranslator tmptrans = new TemporalTranslator(formula, bounds, options);
		Formula extformula = tmptrans.translate();
		Proc proc = null;
		PardinusBounds extbounds = null;
		extbounds = tmptrans.expand(k);
		extbounds.ensureAtomRelations();
		proc = Translator.translate2proc(extformula, extbounds, options);
		return new TemporalHOLTranslation(proc,k,tmptrans.past_depth,extformula,extbounds,formula,bounds,options);
	}

	public static Relation findSkolemRelation(Collection<Relation> holSkolems, Variable variable) {
		for (Relation r: holSkolems)
			if (r.getSkolemVar() == variable)
				return r;
		assert false : "Skolem relation not found for variable " + variable;
		return null;
	}

	/**
	 * Given a quantified formula, replace occurrences of quantified variables by the concrete values of a given instance.
	 * @param form
	 * @param inst
	 * @param extbounds
	 * @param bounds
	 * @param options
	 * @return
	 */
	private static Formula extendFormulas(Formula form, TemporalInstance inst, PardinusBounds extbounds, PardinusBounds bounds, ExtendedOptions options) {
		final Map<Variable,Expression> varmap = new HashMap<Variable,Expression>();
		QuantifiedFormula qf = (QuantifiedFormula) form;
		for (Decl d : qf.decls()) {
			Relation sk = findSkolemRelation(inst.state(0).relations(), d.variable());
			TupleSet skTuples = inst.tuples(sk.name());
			if (skTuples == null)
				return null;

			varmap.put(d.variable().isVariable()?d.variable().getExpansion():d.variable(), extbounds.ts2expr(skTuples));
		}
		Formula extadd = cache.get(qf.formula());

		if (extadd == null) {
			TemporalTranslator _tmptrans = new TemporalTranslator(qf.formula(), bounds, options);
			extadd = _tmptrans.translate();
			extadd = ((BinaryFormula) ((BinaryFormula) extadd).right()).left();
			Formula loops = TemporalTranslator.LOOP.eq(extbounds.ts2expr(inst.tuples(TemporalTranslator.LOOP))).not();
			for (TupleSet l : inst.alt_loops) {
				loops = loops.and(TemporalTranslator.LOOP.eq(extbounds.ts2expr(l)).not());
			}

			extadd = extadd.or(loops);
		}

		Formula fInc = (extadd.accept(new AbstractReplacer(new HashSet<Node>()) {
			@Override
			public Expression visit(Variable variable) {
				Expression expr = varmap.get(variable);
				if (expr == null)
					return super.visit(variable);
				if (expr == Expression.NONE)
					for (int i = 1; i < variable.arity(); i++)
						expr = expr.product(Expression.NONE);
				return expr;
			}
		}));
		Pair<Formula,Bounds> ns = HOLTranslator.toProc(fInc, extbounds, options).firstOrderProblem();
		fInc = ns.a;
		for (Relation r : ns.b.relations())
			if (!extbounds.relations().contains(r))
				extbounds.bound(r, ns.b.lowerBound(r), ns.b.upperBound(r));
		
		return FullNegationPropagator.toNNF(AnnotatedNode.annotateRoots(fInc)).node();
	}

	public static TemporalTranslation nextStep(TemporalTranslation tmptrans) {
		tmptrans.traceInc();
		// this could be reused if stored
		TemporalTranslator t = new TemporalTranslator(tmptrans.formula(), tmptrans.bounds(), tmptrans.options());

		PardinusBounds extbounds = t.expand(tmptrans.traceLength(),tmptrans.cand);
		extbounds.ensureAtomRelations();
		Formula exp_reforms = t.translate();

		// needed for HOL
		for (Formula f : tmptrans.adds.keySet())
			for (TemporalInstance i : tmptrans.adds.get(f)) {
				if (i.prefixLength() <= tmptrans.traceLength()) {
					i = i.unrollStep(tmptrans.traceLength(),tmptrans.pastDepth()).iterator().next();
					Formula ext = extendFormulas(f,i,extbounds,tmptrans.bounds(),tmptrans.options());
					exp_reforms = exp_reforms.and(ext);
				} else {
					System.out.println("Ignoring %d because at %d.".formatted(i.prefixLength(),tmptrans.traceLength()));
				}
			}

		Translation translation = Translator.translateIncremental(exp_reforms, extbounds, tmptrans.options());
//        if (tmptrans.options().logTranslation() > 0)
//            translation.log().logTempTranslation(t.tempTransLog);

		TemporalTranslation ntmp = new TemporalTranslation(translation,tmptrans.traceLength(),tmptrans.pastDepth(),exp_reforms,extbounds,tmptrans.formula(),tmptrans.bounds(),tmptrans.options(),tmptrans.cand,tmptrans.adds);
		ntmp.addSeenSol(tmptrans.seenSols());

        for (IterationStep inst : ntmp.seenSols()) {
            final List<int[]> notModel = instanceToSat(ntmp,inst);
            for (int[] cnfs : notModel)
                translation.cnf().addClause(cnfs);
        }
		return ntmp;

	}
    
    public static TemporalTranslation translateNext(TemporalTranslation trans) {
        TemporalTranslator tmptrans = new TemporalTranslator(trans.formula(), trans.bounds(), trans.options());
        Formula exp_reforms = tmptrans.translate();
        PardinusBounds extbounds = tmptrans.expand(trans.traceLength());
		extbounds.ensureAtomRelations();

		Translation translation = Translator.translateIncremental(exp_reforms, extbounds, trans.options());
		TemporalTranslation tmptrn = new TemporalTranslation(translation,trans.traceLength(),trans.pastDepth(),exp_reforms,extbounds,trans.formula(),trans.bounds(),trans.options(),trans.cand,trans.adds);
		tmptrn.addSeenSol(trans.seenSols());

        for (IterationStep inst : trans.seenSols()) {
            final List<int[]> notModel = instanceToSat(tmptrn,inst);
            for (int[] cnfs : notModel)
                translation.cnf().addClause(cnfs);
        }

      //  if (trans.options().logTranslation() > 0)
      //      translation.log().logTempTranslation(tmptrans.tempTransLog);

        return tmptrn;
    }

    public static TemporalTranslation translateNextFormula(TemporalTranslation trans, int state, TemporalInstance inst) {
        TemporalTranslator tmptrans = new TemporalTranslator(trans.formula().and(trans.reforms()), trans.bounds(), trans.options());
        Formula exp_reforms = tmptrans.translate();
        PardinusBounds extbounds = tmptrans.expand(trans.traceLength());
        
        // this freezes the prefix at the bound level
        TemporalBoundsExpander.extend(trans.bounds(), extbounds, state < 0 ? 0 : state, trans.traceLength(),
                inst);

		Translation translation = Translator.translateIncremental(exp_reforms, extbounds, trans.options());
		// if (trans.options().logTranslation() > 0)
        //     translation.log().logTempTranslation(tmptrans.tempTransLog);

		TemporalTranslation tmptrn = new TemporalTranslation(translation,trans.traceLength(),trans.pastDepth(),exp_reforms,extbounds,trans.formula(),trans.bounds(),trans.options(),trans.cand,trans.adds);
        tmptrn.addSeenSol(trans.seenSols());
        return tmptrn;
    }

    public static void remove(TemporalTranslation tmptrans, TemporalInstance previousSol, int state, int steps, Set<Relation> fix, Set<Relation> change) {
        IterationStep newstep = new IterationStep(previousSol, state, (steps == -1) ? -1 : (state + steps - 1), new HashSet<Relation>(fix), new HashSet<Relation>(change));
        tmptrans.addSeenSol(newstep);
        final List<int[]> notModel = instanceToSat(tmptrans,newstep);
        for (int[] cnfs : notModel)
            tmptrans.cnf().addClause(cnfs);
    }

    // alternative encodings, atom reification vs some disj pattern
    public static boolean SomeDisjPattern = false;


    public static void removeFormula(TemporalTranslation trans, TemporalInstance previousSol, int state, int steps, Set<Relation> fix, Set<Relation> change) {
        IterationStep newstep = new IterationStep(previousSol, state, state + steps - 1, fix, change);
        
        trans.addSeenSol(newstep);   
        
        Formula reforms = Formula.TRUE;
        for (IterationStep i : trans.seenSols()) {
            Formula reform = i.prev.formulate(trans.bounds(), trans.reifs, trans.formula(), i.start,
                    i.end == -1 ? null : i.start + i.end - 1, SomeDisjPattern);
            trans.options().reporter().debug("Negated instance: " + reform);
            reforms = reforms.and(reform.not());
        }
        
        trans.setReforms(reforms);
    }

    public static class IterationStep {
        final TemporalInstance prev;
        final int start, end;
        final Set<Relation> fix, change;
        final boolean infinite;

        private IterationStep(TemporalInstance prev, int start, int end, Set<Relation> fix, Set<Relation> change) {
            super();
            this.prev = prev;
            this.start = start;
            this.end = end;
            this.fix = fix;
            this.change = change;
            this.infinite = end == -1;
        }
    }
    

    /**
     * Converts an iteration step into its SAT negation for the current prefix
     * length. Takes into consideration all equivalent loops for an unrolled
     * instance.
     */
    private static List<int[]> instanceToSat(TemporalTranslation tmptrans, IterationStep inst) {
        int past_depth = countHeight(tmptrans.formula());

        Options opt = tmptrans.options();
        int current_trace = tmptrans.traceLength();
        PardinusBounds bounds = tmptrans.extBounds();
        
        List<int[]> res = new ArrayList<>();
        // if the current prefix length cannot accommodate the iteration, return unsat
        if ((!inst.infinite && inst.end + 1 > current_trace) || inst.start > current_trace)
            return Collections.singletonList(new int[] {});
        // the end of the change/fix segment depends on whether infinite or not
        int segment_end = inst.infinite ? current_trace : inst.end;
        // unroll the temporal instance given the current prefix length and past op
        // depth
        Set<TemporalInstance> alt_loops = inst.prev.unrollStep(current_trace, past_depth);
        opt.reporter().debug("Iteration at " + current_trace + " between " + inst.start + " and " + segment_end);
        opt.reporter().debug("Expanding and negating previous instance, " + alt_loops.size()
                + " possible unroll(s):\n" + inst.prev);
        // only the looping state changes, so any instance can be used for encoding
        // states
        TemporalInstance instance = alt_loops.iterator().next();
        List<Integer> notModel = new ArrayList<Integer>();
        // identify and negate the variables denoting the states
        for (Relation r : bounds.relations()) {
            // check whether any changing/fixing restriction on r
            Boolean pos = null;
            if (inst.change.stream().map(x -> x.isVariable() ? x.getExpansion() : x).anyMatch(x -> x == r))
                pos = false;
            if (inst.fix.stream().map(x -> x.isVariable() ? x.getExpansion() : x).anyMatch(x -> x == r))
                if (pos != null)
                    throw new IllegalArgumentException("Cannot fix and change " + r);
                else
                    pos = true;
            TupleSet lower = bounds.lowerBound(r);
            IntSet vars = tmptrans.primaryVariables(r);
            opt.reporter().debug("Vars per state for " + r + ": " + vars.size() / current_trace);
            opt.reporter().debug(
                    r + " has vars " + vars + " and upper " + bounds.upperBound(r).indexView());
            if (!vars.isEmpty() && !r.equals(TemporalTranslator.LOOP) && !r.equals(TemporalTranslator.STATE)
                    && !r.equals(TemporalTranslator.PREFIX) && instance.tuples(r) != null) {
                opt.reporter().debug(bounds.upperBound(r).indexView() + " vs "
                        + instance.tuples(r).indexView() + "");
                int lit = vars.min();
                for (IntIterator iter = bounds.upperBound(r).indexView().iterator(); iter
                        .hasNext();) {
                    final int index = iter.next();
                    if (!lower.indexView().contains(index)) {
                        // this infers the state of a variable assuming that they are created state-wise
                        // and that each state has the same number of variables (since the bounds are
                        // the same of all trace, should be true)
                        if (!tmptrans.bounds().relations().contains(r)) {
                            int idx = (lit - vars.min()) % current_trace;
                            if (pos != null && idx >= inst.start && idx <= segment_end) {
                                if (!pos)
                                    notModel.add(instance.tuples(r).indexView().contains(index) ? -lit : lit);
                                else
                                    res.add(new int[] {
                                            instance.tuples(r).indexView().contains(index) ? lit : -lit });
                            } else if (idx < inst.start)
                                // if before change segment, fix variable
                                res.add(new int[] { instance.tuples(r).indexView().contains(index) ? lit : -lit });
                        } else {
                            if (inst.start > 0 || (pos != null && pos))
                                res.add(new int[] { instance.tuples(r).indexView().contains(index) ? lit : -lit });
                            if (pos != null && !pos)
                                notModel.add(instance.tuples(r).indexView().contains(index) ? -lit : lit);
                        }
                        lit++;
                    }
                }
                opt.reporter().debug(notModel + "");
            }
        }
        opt.reporter().debug("New clause without loops");
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < notModel.size(); i++)
            sb.append(notModel.get(i) + " ");
        opt.reporter().debug(sb.toString());
        // loops only relevant when infinite iteration
        if (inst.infinite) {
            // identify and negate the relevant loop variables
            Set<Integer> loops = new HashSet<Integer>();
            IntSet vars = tmptrans.primaryVariables(TemporalTranslator.LOOP);
            opt.reporter().debug(vars.toString());
            // for each of the possible loops, identify the primary variable
            for (TemporalInstance i : alt_loops) {
                int lit = vars.min();
                for (int j = 0; j < i.loop; j++)
                    lit++;
                loops.add(lit);
            }
            opt.reporter().debug("Bad loops were " + loops);
            for (IntIterator iter = vars.iterator(); iter.hasNext();) {
                final int lit = iter.next();
                if (!loops.contains(lit))
                    notModel.add(lit);
            }
        }
        opt.reporter().debug("New final clause");
        sb = new StringBuilder();
        for (int k = 0; k < notModel.size(); k++)
            sb.append(notModel.get(k));
        opt.reporter().debug(sb.toString());
        for (int[] x : res)
            opt.reporter().debug(x[0] + "");

        // empty notModel in finite just means no changed forced; however, if empty in
        // infinite not possible loop, so unsat
        if (!notModel.isEmpty() || inst.infinite)
            res.add(notModel.stream().mapToInt(ii -> ii).toArray());

        return res;
    }

    public static void trivial(TemporalTranslation tmptrans, Formula formula, Bounds newBounds) {
		tmptrans.translation = Translator.translateIncremental(formula, newBounds, tmptrans.options());
	}

}
