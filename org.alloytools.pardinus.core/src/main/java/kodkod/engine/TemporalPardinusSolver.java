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
package kodkod.engine;

import java.io.BufferedOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.TargetOptions.TMode;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.TranslationLog;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.fol2sat.UnboundLeafException;
import kodkod.engine.ltl2fol.TemporalBoundsExpander;
import kodkod.engine.ltl2fol.TemporalTranslation;
import kodkod.engine.ltl2fol.TemporalTranslator;
import kodkod.engine.ltl2fol.TemporalTranslator.IterationStep;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATProver;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.satlab.TargetSATSolver;
import kodkod.engine.satlab.WTargetSATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntSet;
import kodkod.util.nodes.PrettyPrinter;

/**
 * A temporal solver relying on Kodkod.
 *
 * The solver is responsible by iteratively increasing the bounded trace length
 * up to the maximum defined in the options. Adapted from {@link kodkod.engine.Solver}.
 *
 * @author Nuno Macedo // [HASLab] target-oriented and temporal model finding
 */
public final class TemporalPardinusSolver
		implements KodkodSolver<PardinusBounds, ExtendedOptions>, TemporalSolver<ExtendedOptions>, ExplorableSolver<PardinusBounds, ExtendedOptions> {

	// alternative encodings, instance formula or sat
	public static boolean SATOPTITERATION = true;

	private final ExtendedOptions options;

	/**
	 * Constructs a new Solver with the default options.
	 *
	 * @ensures this.options' = new Options()
	 */
	public TemporalPardinusSolver() {
		this.options = new ExtendedOptions();
	}

	/**
	 * Constructs a new Solver with the given options.
	 *
	 * @ensures this.options' = options
	 * @throws NullPointerException
	 *             options = null
	 */
	public TemporalPardinusSolver(ExtendedOptions options) {
		if (options == null)
			throw new NullPointerException();

		this.options = options;
	}

	/**
	 * Returns the Options object used by this Solver to guide translation of
	 * formulas from first-order logic to cnf.
	 *
	 * @return this.options
	 */
	public ExtendedOptions options() {
		return options;
	}

	/**
	 * {@inheritDoc}
	 *
	 * @see kodkod.engine.KodkodSolver#free()
	 */
	public void free() {
	}

	// [HASLab]
	public Solution solve(Formula formula, PardinusBounds bounds) throws HigherOrderDeclException,
			UnboundLeafException, AbortedException {
		assert !options.unbounded();
		try {
			boolean isSat = false;

			long startTransl = System.currentTimeMillis();
			TemporalTranslation tmptrans = TemporalTranslator.translate(formula, bounds, options);
			long endTransl = System.currentTimeMillis();
			long transTime = endTransl - startTransl;

			long solveTime = 0;
			if (tmptrans.trivial() && tmptrans.traceLength() == options.maxTraceLength())
				return trivial(tmptrans, endTransl - startTransl);

			SATSolver cnf = tmptrans.cnf();

			options.reporter().solvingCNF(tmptrans.traceLength(), tmptrans.numPrimaryVariables(), cnf.numberOfVariables(),
					cnf.numberOfClauses());
			long startSolve = System.currentTimeMillis();
			isSat = cnf.solve();
			long endSolve = System.currentTimeMillis();
			solveTime = endSolve - startSolve;
			final Statistics stats = new Statistics(tmptrans, transTime, solveTime);

			while (!isSat && tmptrans.traceLength() < options.maxTraceLength()) {
				startTransl = System.currentTimeMillis();
				tmptrans = TemporalTranslator.nextStep(tmptrans);
				endTransl = System.currentTimeMillis();
				transTime = endTransl - startTransl;

				cnf = tmptrans.cnf();

				options.reporter().solvingCNF(tmptrans.traceLength(), tmptrans.numPrimaryVariables(), cnf.numberOfVariables(),
						cnf.numberOfClauses());
				startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				endSolve = System.currentTimeMillis();
				solveTime = endSolve - startSolve;

				stats.update(tmptrans, transTime, solveTime);
			}
			return isSat ? sat(tmptrans, stats, bounds) : unsat(tmptrans, stats);
		} catch (SATAbortedException sae) {
			throw new AbortedException(sae);
		}
	}

	public Explorer<Solution> solveAll(Formula formula, PardinusBounds bounds) throws HigherOrderDeclException,
			UnboundLeafException, AbortedException {
		if (Options.isDebug())
			flushFormula(formula, bounds); // [AM]

		// [HASLab] this was commented, why?
		if (!options.solver().incremental())
			throw new IllegalArgumentException("cannot enumerate solutions without an incremental solver.");

		if (options instanceof ExtendedOptions && options.targetoriented())
			return new TSolutionIterator(formula, bounds, options); // [HASLab]
		else
			return new SolutionIterator(formula, bounds, options);
	}

	// [AM]
	private void flushFormula(Formula formula, Bounds bounds) {
		try {
			File f = new File(System.getProperty("java.io.tmpdir"), "kk.txt");
			try (OutputStream os = new BufferedOutputStream(new FileOutputStream(f))) {
				os.write(PrettyPrinter.print(formula, 2).getBytes());
				os.write("\n================\n".getBytes());
				os.write(bounds.toString().getBytes());
			}
		} catch (Exception e) {
		}
	}

	/**
	 * {@inheritDoc}
	 *
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return options.toString();
	}
	
    public static Solution solveTranslation(final long translTime, final Translation translation) {
        final Solution solution;
        if (translation.trivial()) {
            final Statistics stats = new Statistics(translation, translTime, 0);
            if (translation.cnf().solve()) {
                solution = Solution.triviallySatisfiable(stats, new TemporalInstance(translation.interpret(),(PardinusBounds) translation.bounds()));
            } else {
                solution = Solution.triviallyUnsatisfiable(stats, null);
            }
        } else {
            final SATSolver cnf = translation.cnf();

            translation.options().reporter().solvingCNF(0,translation.numPrimaryVariables(), cnf.numberOfVariables(), cnf.numberOfClauses());
            final long startSolve = System.currentTimeMillis();
            final boolean sat = cnf.solve();
            final long endSolve = System.currentTimeMillis();

            final Statistics stats = new Statistics(translation, translTime, endSolve - startSolve);
            if (sat) {
                solution = Solution.satisfiable(stats,  new TemporalInstance(translation.interpret(),(PardinusBounds) translation.bounds()));
            } else {
                solution = Solution.unsatisfiable(stats, null);
            }
        }
        return solution;
    }

	// [HASLab]
	private static Solution sat(TemporalTranslation translation, Statistics stats, PardinusBounds originalBounds) {
		final Solution sol = Solution.satisfiable(stats, new TemporalInstance(translation.interpretStatic(),originalBounds));
		translation.cnf().free();
		return sol;
	}

	// [HASLab]
	private static Solution unsat(TemporalTranslation translation, Statistics stats) {
		final SATSolver cnf = translation.cnf();
		final TranslationLog log = translation.log();
		if (cnf instanceof SATProver && log != null) {
			return Solution.unsatisfiable(stats, new ResolutionBasedProof((SATProver) cnf, log));
		} else { // can free memory
			final Solution sol = Solution.unsatisfiable(stats, null);
			cnf.free();
			return sol;
		}
	}

	// [HASLab]
	private static Solution trivial(TemporalTranslation translation, long translTime) {
		final Statistics stats = new Statistics(0, 0, 0, translTime, 0);
		final Solution sol;
		if (translation.cnf().solve()) {
			sol = Solution.triviallySatisfiable(stats, new TemporalInstance(translation.interpret(),translation.extBounds()));
		} else {
			sol = Solution.triviallyUnsatisfiable(stats, trivialProof(translation.log()));
		}
		translation.cnf().free();
		return sol;
	}

	/**
	 * Returns a proof for the trivially unsatisfiable log.formula, provided
	 * that log is non-null. Otherwise returns null.
	 *
	 * @requires log != null => log.formula is trivially unsatisfiable
	 * @return a proof for the trivially unsatisfiable log.formula, provided
	 *         that log is non-null. Otherwise returns null.
	 */
	private static Proof trivialProof(TranslationLog log) {
		return log == null ? null : new TrivialProof(log);
	}

	/**
	 * An iterator over all solutions of a model.
	 *
	 * @author Nuno Macedo // [HASLab] temporal model finding
	 */
	private final static class SolutionIterator implements Explorer<Solution> {
		private long translTime;
		private int trivial;
		private final ExtendedOptions opt; // [HASLab] temporal
		private final PardinusBounds originalBounds;
		private final Formula originalFormula;
		private TemporalTranslation tmptrans;

		// [HASLab] structures for reformulated iteration
		private TemporalInstance previousSol = null;

		SolutionIterator(Formula formula, PardinusBounds bounds, ExtendedOptions options) { // [HASLab]
			assert !options.unbounded();
			this.translTime = System.currentTimeMillis();
			this.originalBounds = bounds;
			this.originalFormula = formula;

			tmptrans = TemporalTranslator.translate(originalFormula, bounds, options);

			this.translTime = System.currentTimeMillis() - translTime;
			this.trivial = 0;
			this.opt = options;
		}


		/**
		 * Returns true if there is another solution.
		 *
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return hasNextP();
		}

		public boolean hasNextC() {
			return !(iteration_stage == 0 && tmptrans.isClear());
		}

		public boolean hasNextP() {
			return !(iteration_stage == 1 && tmptrans.isClear()) && hasNextC();
		}

		/**
		 * Returns the next solution if any.
		 *
		 * @see java.util.Iterator#next()
		 */
		public Solution nextS(int state, int delta, Set<Relation> change) {
			if (delta < 1)
				throw new IllegalArgumentException("Cannot iterate boundless with s != 0, breaks completeness.");

			if (tmptrans.isClear() && !(iteration_stage == 2 && state < last_segment))
				return Solution.triviallyUnsatisfiable(new Statistics(0, 0, 0, 0, 0), null);
			try {
				Set<Relation> fix = new HashSet<Relation>();
				if (iteration_stage == 0) // only fix config once
					fix.addAll(tmptrans.bounds().relations().stream().filter(r -> !r.isVariable())
							.collect(Collectors.toSet()));

				// if reducing prefix, restart the process
				// this will force the re-generation of the solver at minimal length
				if (iteration_stage == 2 && state < last_segment) {
					tmptrans.removeSeenFromSols(state);
					tmptrans.clear();
				}

				if (previousSol != null)
					iteration_stage = 2;

				last_segment = state;
				return (tmptrans != null && tmptrans.trivial()) ? nextTrivialSolution() : nextNonTrivialSolution(state, delta, fix, change);
			} catch (SATAbortedException sae) {
				tmptrans.cnf().free();
				throw new AbortedException(sae);
			}
		}

		public Solution nextP() {
			if (iteration_stage == 2)
				throw new IllegalArgumentException(
						"Cannot iterate boundless after segment iteration, breaks completeness.");

			if (!hasNext())
				throw new NoSuchElementException();
			try {
				Set<Relation> fix = new HashSet<Relation>();
				if (iteration_stage == 0) // only fix config once
					fix.addAll(tmptrans.bounds().relations().stream().filter(r -> !r.isVariable())
							.collect(Collectors.toSet()));

				Set<Relation> change = tmptrans.bounds().relations().stream().filter(r -> r.isVariable())
						.collect(Collectors.toSet());

				if (previousSol != null)
					iteration_stage = 1;

				return tmptrans.trivial() ? nextTrivialSolution() : nextNonTrivialSolution(0, -1, fix, change);
			} catch (SATAbortedException sae) {
				tmptrans.cnf().free();
				throw new AbortedException(sae);
			}
		}

		public Solution nextC() {
			// if unsat on other mode, can still try new config
			if (iteration_stage == 0 && !hasNext())
				throw new NoSuchElementException();
			try {
				Set<Relation> fix = new HashSet<Relation>();
				Set<Relation> change = originalBounds.relations().stream().filter(r -> !r.isVariable())
						.collect(Collectors.toSet());

				// if coming back from other mode, restart the process
				// this will force the re-generation of the solver at minimal length
				if (iteration_stage != 0) {
					tmptrans.removeSeenFromSols(-1);
					tmptrans.clear();
				}

				iteration_stage = 0;

				return (tmptrans != null && tmptrans.trivial()) ? nextTrivialSolution() : nextNonTrivialSolution(-1, 0, fix, change);
			} catch (SATAbortedException sae) {
				tmptrans.cnf().free();
				throw new AbortedException(sae);
			}
		}

		/**
		 * Returns the next solution if any.
		 *
		 * @see java.util.Iterator#next()
		 */
		public Solution next() {
			return nextP();
		}

		/** @throws UnsupportedOperationException */
		public void remove() {
			throw new UnsupportedOperationException();
		}

		/**
		 * Solves {@code translation.cnf} and adds the negation of the found model to
		 * the set of clauses. The latter has the effect of forcing the solver to come
		 * up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets {@code this.translation}
		 * to null.
		 *
		 * @requires this.translation != null
		 * @ensures this.translation.cnf is modified to eliminate the current
		 *          solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextNonTrivialSolution(int state, int steps, Set<Relation> fix, Set<Relation> change) {
			if (SATOPTITERATION)
				return nextNonTrivialSolutionSAT(state, steps, fix, change);
			else
				return nextNonTrivialSolutionFormula(state, steps, fix, change);
		}

		private int iteration_stage = 0;
		private int last_segment = 0;

		private Solution nextNonTrivialSolutionSAT(int state, int steps, Set<Relation> fix, Set<Relation> change) {
			if (previousSol != null && change.isEmpty()) {
				tmptrans.clear();
				return Solution.unsatisfiable(new Statistics(0, 0, 0, 0, 0), null);
			}

			boolean isSat = false;
			long solveTime = 0;
			TemporalTranslation transl = null;
			int primaryVars = -1;
			SATSolver cnf = null;

			// this may be coming from an unsat path iteration and must be restarted before
			// the previous solution is converted into sat
			if (tmptrans.isClear()) {

				long translStart = System.currentTimeMillis();

				// the translation of the original formula could in principle be re-used but
				// the original past depth level is needed
				tmptrans = TemporalTranslator.translateNext(tmptrans);

				long translEnd = System.currentTimeMillis();
				translTime += translEnd - translStart;

			}

			// instance negation must now occur on the next step since the operation is not
			// known a priori
			if (previousSol != null) {
				TemporalTranslator.remove(tmptrans,previousSol,state,steps,fix,change);
			}

			final Statistics stats = new Statistics(0, 0, 0, 0, 0);

			while (!isSat && tmptrans.traceLength() <= opt.maxTraceLength()) {
				if (tmptrans.isClear()) {
					long translStart = System.currentTimeMillis();

					// the translation of the original formula could in principle be re-used but
					// the original past depth level is needed
					tmptrans = TemporalTranslator.translateNext(tmptrans);

					long translEnd = System.currentTimeMillis();
					translTime = translEnd - translStart;
				}

				transl = tmptrans;

				cnf = transl.cnf();
				primaryVars = transl.numPrimaryVariables();

				transl.options().reporter().solvingCNF(tmptrans.traceLength(), primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

				final long startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				final long endSolve = System.currentTimeMillis();
				solveTime = endSolve - startSolve;

				stats.update(transl, translTime, solveTime);

				if (!isSat) {
					tmptrans.traceInc();
				}
			}

			final Solution sol;

			if (isSat) {
				// extract the current solution; can't use the sat(..) method
				// because it frees the sat solver
				sol = Solution.satisfiable(stats, new TemporalInstance(transl.interpretStatic(), originalBounds));

//				// [HASLab] skolems are not used in temporal iteration
//				IntSet tempskolemvars = new IntTreeSet();
//				for (Relation r : transl.bounds().relations())
//					if (r.isSkolem() && opt.temporal())
//						tempskolemvars.addAll(transl.primaryVariables(r));
//
//				// add the negation of the current model to the solver
//				final int[] notModel = new int[primaryVars - tempskolemvars.size()];
//				for (int i = 1; i <= primaryVars; i++) {
//					if (!tempskolemvars.contains(i))
//						notModel[i - 1] = cnf.valueOf(i) ? -i : i;
//				}
				// [HASLab] store the reformulated instance
				// NOTE: should be on next to also get trivials?
				previousSol = (TemporalInstance) sol.instance();

			} else {
				sol = unsat(transl, stats); // this also frees up solver resources, if any
				tmptrans.clear(); // unsat, no more solutions
			}

			return sol;
		}

		private Solution nextNonTrivialSolutionFormula(int state, int steps, Set<Relation> fix, Set<Relation> change) {

			boolean isSat = false;
			long solveTime = 0;
			TemporalTranslation transl = null;
			int primaryVars = -1;
			SATSolver cnf = null;

			if (previousSol != null)
				TemporalTranslator.removeFormula(tmptrans,previousSol,state,steps,fix,change);


			while (!isSat && tmptrans.traceLength() <= opt.maxTraceLength()) {
				// this operation must restart the process since the branching formula is
				// ephemeral

				long translStart = System.currentTimeMillis();

				tmptrans = TemporalTranslator.translateNextFormula(tmptrans,state,previousSol);

				long translEnd = System.currentTimeMillis();
				translTime += translEnd - translStart;

				transl = tmptrans;

				cnf = transl.cnf();
				primaryVars = transl.numPrimaryVariables();

				transl.options().reporter().solvingCNF(transl.traceLength(), primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

				final long startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				final long endSolve = System.currentTimeMillis();
				solveTime += endSolve - startSolve;

				if (!isSat)
					transl.traceInc();
			}

			final Statistics stats = new Statistics(transl, translTime, solveTime);

			final Solution sol;

			if (isSat) {
				// extract the current solution; can't use the sat(..) method
				// because it frees the sat solver
				sol = Solution.satisfiable(stats, new TemporalInstance(transl.interpret(), originalBounds));

				// store the reformulated instance
				// NOTE: should be on next to also get trivials?
				previousSol = (TemporalInstance) sol.instance();
			} else {
				sol = unsat(transl, stats); // this also frees up solver resources, if any
				tmptrans.clear(); // unsat, no more solutions
			}
			return sol;
		}

		/**
		 * Returns the trivial solution corresponding to the trivial translation
		 * stored in {@code this.translation}, and if
		 * {@code this.translation.cnf.solve()} is true, sets
		 * {@code this.translation} to a new translation that eliminates the
		 * current trivial solution from the set of possible solutions. The
		 * latter has the effect of forcing either the translator or the solver
		 * to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 *
		 * @requires this.translation != null
		 * @ensures this.translation is modified to eliminate the current
		 *          trivial solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextTrivialSolution() {
			final TemporalTranslation transl = this.tmptrans;

			final Solution sol = trivial(transl, translTime); // this also frees up solver resources, if unsat

			if (sol.instance() == null) {
				tmptrans.clear(); // unsat, no more solutions
			} else {
				trivial++;

				final Bounds bounds = transl.bounds();
				final Bounds newBounds = bounds.clone();
				final List<Formula> changes = new ArrayList<Formula>();

				for (Relation r : bounds.relations()) {
					final TupleSet lower = bounds.lowerBound(r);

					if (lower != bounds.upperBound(r)) { // r may change
						if (lower.isEmpty()) {
							changes.add(r.some());
						} else {
							final Relation rmodel = Relation.nary(r.name() + "_" + trivial, r.arity());
							newBounds.boundExactly(rmodel, lower);
							changes.add(r.eq(rmodel).not());
						}
					}
				}

				// nothing can change => there can be no more solutions (besides
				// the current trivial one).
				// note that transl.formula simplifies to the constant true with
				// respect to
				// transl.bounds, and that newBounds is a superset of
				// transl.bounds.
				// as a result, finding the next instance, if any, for
				// transl.formula.and(Formula.or(changes))
				// with respect to newBounds is equivalent to finding the next
				// instance of Formula.or(changes) alone.
				final Formula formula = changes.isEmpty() ? Formula.FALSE : Formula.or(changes);

				final long startTransl = System.currentTimeMillis();
				TemporalTranslator.trivial(tmptrans,formula,newBounds);

				translTime += System.currentTimeMillis() - startTransl;
			}
			return sol;
		}

	}

	/**
	 * A target-oriented iterator over all solutions of a model, adapted from {@link SolutionIterator}.
	 * @author Tiago Guimarães, Nuno Macedo // [HASLab] target-oriented, temporal model finding
	 */
	public static class TSolutionIterator implements Explorer<Solution> {
		private TemporalTranslation translation;
		private long translTime;
		private final ExtendedOptions opt; // [HASLab] TO mode
		private Map<String, Integer> weights; // [HASLab] signature weights
		private PardinusBounds originalBounds;

		TSolutionIterator(Formula formula, PardinusBounds bounds, ExtendedOptions options) { // [HASLab]
			if (!options.configOptions().solver().maxsat())
				throw new IllegalArgumentException("A max sat solver is required for target-oriented solving.");
			this.translTime = System.currentTimeMillis();
			this.originalBounds = bounds;
			translation = TemporalTranslator.translate(formula, bounds, options);
			this.translTime = System.currentTimeMillis() - translTime;
			this.opt = options;
		}

		/**
		 * Returns true if there is another solution.
		 *
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {
			return translation != null;
		}

		/**
		 * Returns the next solution if any.
		 *
		 * @see java.util.Iterator#next()
		 */
		public Solution next() {
			if (!hasNext())
				throw new NoSuchElementException();
			// TODO [HASLab]: trivial solutions not yet supported in TO
			if (translation.trivial())
				throw new RuntimeException("Trivial problems with targets not yet supported.");
			else
				try {
					return translation.trivial() ? nextTrivialSolution() : nextNonTrivialSolution();
				} catch (SATAbortedException sae) {
					translation.cnf().free();
					throw new AbortedException(sae);
				}
		}

		/** @throws UnsupportedOperationException */
		public void remove() {
			throw new UnsupportedOperationException();
		}

		/**
		 * Solves {@code translation.cnf} and adds the negation of the found
		 * model to the set of clauses. The latter has the effect of forcing the
		 * solver to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 *
		 * @requires this.translation != null
		 * @ensures this.translation.cnf is modified to eliminate the current
		 *          solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextNonTrivialSolution() {
			final TMode mode = opt.targetMode();
			boolean isSat = false;
			int traceLength = opt.minTraceLength();
			long solveTime = 0;
			TemporalTranslation transl = null;
			int primaryVars = -1;
			SATSolver cnf = null;
			while (!isSat && traceLength <= opt.maxTraceLength()) {
				if (traceLength > 1) {
					long translStart = System.currentTimeMillis();
					transl = TemporalTranslator.translateNext(transl);
					long translEnd = System.currentTimeMillis();
					translTime += translEnd - translStart;
				}
				transl = translation;

				cnf = transl.cnf();
				primaryVars = transl.numPrimaryVariables();
				// [HASLab] add the targets to generate the following
				// solution due to the architecture of Alloy, targets are added
				// directly
				// to the SAT rather than through the bounds
				try {
					cnf.valueOf(1); // fails if no previous solution
					final int[] notModel = new int[primaryVars];
					if (mode.equals(TMode.CLOSE) || mode.equals(TMode.FAR)) {
						TargetSATSolver tcnf = (TargetSATSolver) cnf;
						tcnf.clearTargets();
						// [HASLab] if there are weights must iterate
						// through the relations to find the literal's owner
						if (weights != null) {
							WTargetSATSolver wcnf = (WTargetSATSolver) cnf;
							for (Relation r : transl.bounds().relations()) {
								Integer w = weights.get(r.name());
								if (r.name().equals("Int/next") || r.name().equals("seq/Int")
										|| r.name().equals("String")) {
								} else {
									if (w == null) {
										w = 1;
									}
									IntIterator is = transl.primaryVariables(r).iterator();
									while (is.hasNext()) {
										int i = is.next();
										// add the negation of the current model
										// to the solver
										notModel[i - 1] = cnf.valueOf(i) ? -i : i;
										// [HASLab] add current model
										// as weighted targe)t
										if (mode == TMode.CLOSE)
											wcnf.addWeight(cnf.valueOf(i) ? i : -i, w);
										if (mode == TMode.FAR)
											wcnf.addWeight(cnf.valueOf(i) ? -i : i, w);
									}
								}
							}
						}
						// [HASLab] if there are no weights may simply
						// iterate literals
						else {
							for (int i = 1; i <= primaryVars; i++) {
								// add the negation of the current model to the
								// solver
								notModel[i - 1] = cnf.valueOf(i) ? -i : i;
								// [HASLab] add current model as target
								if (mode == TMode.CLOSE)
									tcnf.addTarget(cnf.valueOf(i) ? i : -i);
								if (mode == TMode.FAR)
									tcnf.addTarget(cnf.valueOf(i) ? -i : i);
							}
						}

					} else {
						for (int i = 1; i <= primaryVars; i++) {
							// add the negation of the current model to the
							// solver
							notModel[i - 1] = cnf.valueOf(i) ? -i : i;
						}
					}
					cnf.addClause(notModel);
				} catch (IllegalStateException e) {
				} catch (Exception e) {
					throw e;
				}

				opt.reporter().solvingCNF(0, primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());

				final long startSolve = System.currentTimeMillis();
				isSat = cnf.solve();
				final long endSolve = System.currentTimeMillis();
				solveTime += endSolve - startSolve;
			}
			final Statistics stats = new Statistics(transl, translTime, solveTime);
			final Solution sol;

			if (isSat) {
				// extract the current solution; can't use the sat(..) method
				// because it frees the sat solver
				sol = Solution.satisfiable(stats, new TemporalInstance(transl.interpret(),originalBounds));
			} else {
				sol = unsat(transl, stats); // this also frees up solver
				// resources, if any
				translation = null; // unsat, no more solutions
			}
			return sol;
		}

		/**
		 * Returns the trivial solution corresponding to the trivial translation
		 * stored in {@code this.translation}, and if
		 * {@code this.translation.cnf.solve()} is true, sets
		 * {@code this.translation} to a new translation that eliminates the
		 * current trivial solution from the set of possible solutions. The
		 * latter has the effect of forcing either the translator or the solver
		 * to come up with the next solution or return UNSAT. If
		 * {@code this.translation.cnf.solve()} is false, sets
		 * {@code this.translation} to null.
		 *
		 * @requires this.translation != null
		 * @ensures this.translation is modified to eliminate the current
		 *          trivial solution from the set of possible solutions
		 * @return current solution
		 */
		private Solution nextTrivialSolution() {
			throw new UnsupportedOperationException("Trivial target-oriented next not yet supported.");
		}

		/**
		 * Calculates the next TO solutions with weights.
		 *
		 * @param i
		 *            the TO mode
		 * @param weights
		 *            the signature weights
		 */
		// [HASLab]
		public Solution next(Map<String, Integer> weights) {
			if (opt.targetoriented()) {
				if (!(opt.solver().instance() instanceof TargetSATSolver))
					throw new AbortedException("Selected solver (" + opt.solver()
							+ ") does not have support for targets.");
				if (weights != null) {
					if (!(opt.solver().instance() instanceof WTargetSATSolver))
						throw new AbortedException("Selected solver (" + opt.solver()
								+ ") does not have support for targets with weights.");
				}
			}
			this.weights = weights;
			return next();
		}

		@Override
		public Solution nextS(int state, int delta, Set<Relation> force) {
			throw new UnsupportedOperationException("Branching solutions not currently supported.");
		}

		@Override
		public Solution nextC() {
			throw new UnsupportedOperationException("Branching solutions not currently supported.");
		}

		@Override
		public Solution nextP() {
			throw new UnsupportedOperationException("Branching solutions not currently supported.");
		}

		@Override
		public boolean hasNextP() {
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public boolean hasNextC() {
			// TODO Auto-generated method stub
			return false;
		}

	}


}
