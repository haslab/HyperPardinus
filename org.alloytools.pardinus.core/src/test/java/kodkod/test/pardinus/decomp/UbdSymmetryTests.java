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
package kodkod.test.pardinus.decomp;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.engine.Explorer;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.engine.decomp.DModel;
import kodkod.engine.satlab.SATFactory;
import kodkod.examples.pardinus.decomp.SymmetryP;
import kodkod.examples.pardinus.temporal.SymmetryT;
import kodkod.examples.pardinus.temporal.SymmetryT.VariantBounds;
import kodkod.examples.pardinus.temporal.SymmetryT.VariantFormulas;
import kodkod.examples.pardinus.temporal.SymmetryT.VariantOrder;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.util.ints.IntSet;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

/**
 * Tests whether the symmetries are being correctly calculated for decomposed
 * problems by comparing with the amalgamated problem, as well as whether every
 * solution is being enumerated. Also tests problems where either the partial or
 * integrated problem become trivial. Uses the models from {@link SymmetryP}.
 * 
 * @author Nuno Macedo // [HASLab] decomposed model finding
 *
 */
@RunWith(Parameterized.class)
public class UbdSymmetryTests {
	private PardinusSolver dsolver;
	private ExtendedOptions opt;
	private Set<IntSet> last;

	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);

	@Before
	public void method() throws InterruptedException {

		opt = new ExtendedOptions();
		opt.setSymmetryBreaking(20);
		opt.setSolver(SATFactory.DEFAULT);
		opt.setDecomposedMode(DMode.HYBRID);
		opt.setThreads(4);
		Reporter rep = new AbstractReporter() {
			private Bounds bounds;

			@Override
			public void detectingSymmetries(Bounds bounds) {
				super.detectingSymmetries(bounds);
				this.bounds = bounds;
			}

			@Override
			public void detectedSymmetries(Set<IntSet> parts) {
				if (last==null) last = new HashSet<IntSet>(parts);
				Set<Set<Object>> x = new HashSet<Set<Object>>();
				for (IntSet y : parts) {
					Set<Object> z = new HashSet<Object>();
					for (int w : y.toArray())
						z.add(bounds.universe().atom(w));
					x.add(z);
				}
				if (Options.isDebug())
					super.debug("symmetry: " + x.toString());
			}

		};

		opt.setReporter(rep);
	}

	private VariantBounds v1;
	private VariantFormulas v2;
	private VariantOrder v3;

	public UbdSymmetryTests(VariantBounds v1, VariantFormulas v2, VariantOrder v3) {
		this.v1 = v1;
		this.v2 = v2;
		this.v3 = v3;
	}

	@Parameters(name = "{0} {1} {2}")
	public static Collection<Object[]> data() {
		Object[][] data = new Object[][] {
//				{ VariantBounds.V1, VariantFormulas.V1, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V1, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V1, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V1, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V1, VariantOrder.V1 }, // unsat, p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V1, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V2, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  symmetric b2
				{ VariantBounds.V2, VariantFormulas.V2, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V2, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V2, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
				{ VariantBounds.V5, VariantFormulas.V2, VariantOrder.V1 }, // unsat, p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
				{ VariantBounds.V6, VariantFormulas.V2, VariantOrder.V1 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V3, VariantOrder.V1 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V3, VariantOrder.V1 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  asymmetric b2
////				{ VariantBounds.V3, VariantFormulas.V3, VariantOrder.V1 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
////				{ VariantBounds.V4, VariantFormulas.V3, VariantOrder.V1 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V3, VariantOrder.V1 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V3, VariantOrder.V1 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V4, VariantOrder.V1 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V4, VariantOrder.V1 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V4, VariantOrder.V1 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V4, VariantOrder.V1 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V4, VariantOrder.V1 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V4, VariantOrder.V1 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//
//				{ VariantBounds.V1, VariantFormulas.V1, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V1, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V1, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V1, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V1, VariantOrder.V2 }, // unsat, p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V1, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V2, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V2, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V2, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V2, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V2, VariantOrder.V2 }, // unsat, p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V2, VariantOrder.V2 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V3, VariantOrder.V2 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V3, VariantOrder.V2 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V3, VariantOrder.V2 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V3, VariantOrder.V2 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V3, VariantOrder.V2 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V3, VariantOrder.V2 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V4, VariantOrder.V2 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V4, VariantOrder.V2 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V4, VariantOrder.V2 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V4, VariantOrder.V2 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V4, VariantOrder.V2 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V4, VariantOrder.V2 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//
//				{ VariantBounds.V1, VariantFormulas.V1, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V1, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V1, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V1, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V1, VariantOrder.V3 }, // unsat, p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V1, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V2, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V2, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V2, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V2, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V2, VariantOrder.V3 }, // unsat, p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V2, VariantOrder.V3 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V3, VariantOrder.V3 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V3, VariantOrder.V3 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V3, VariantOrder.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V3, VariantOrder.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V3, VariantOrder.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V3, VariantOrder.V3 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V4, VariantOrder.V3 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V4, VariantOrder.V3 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V4, VariantOrder.V3 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V4, VariantOrder.V3 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V4, VariantOrder.V3 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V4, VariantOrder.V3 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//
//				{ VariantBounds.V1, VariantFormulas.V1, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V1, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V1, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V1, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V1, VariantOrder.V4 }, // unsat, p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V1, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V2, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V2, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V2, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V2, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V2, VariantOrder.V4 }, // unsat, p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V2, VariantOrder.V4 }, // sat,   p1 non-trivial, p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V3, VariantOrder.V4 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V3, VariantOrder.V4 }, // sat,   p1 trivial,     p2 non-trivial, symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V3, VariantOrder.V4 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V3, VariantOrder.V4 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V3, VariantOrder.V4 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V3, VariantOrder.V4 }, // sat,   p1 trivial,     p2 non-trivial, asymmetric b1, asymmetric b2
//				{ VariantBounds.V1, VariantFormulas.V4, VariantOrder.V4 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  symmetric b2
//				{ VariantBounds.V2, VariantFormulas.V4, VariantOrder.V4 }, // sat,   p1 trivial,     p2 trivial,     symmetric b1,  asymmetric b2
//				{ VariantBounds.V3, VariantFormulas.V4, VariantOrder.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V4, VariantFormulas.V4, VariantOrder.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, symmetric b2
//				{ VariantBounds.V5, VariantFormulas.V4, VariantOrder.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
//				{ VariantBounds.V6, VariantFormulas.V4, VariantOrder.V4 }, // sat,   p1 trivial,     p2 trivial,     asymmetric b1, asymmetric b2
				};
		return Arrays.asList(data);
	}

//	@Test
//	public void test() {
//		int n = 2;
//
//		String[] args = new String[] { n + "", v1.name(), v2.name(), v3.name() };
//		DModel model = new SymmetryT(args);
//
//		opt.setBitwidth(model.getBitwidth());
//		opt.setRunUnbounded(true);
//		opt.setRunTemporal(true);
//		opt.setNoOverflow(true);
//		opt.setRunDecomposed(true);
//		opt.setSolver(SATFactory.electrod("-t","NuSMV"));
//		opt.setDecomposedMode(DMode.PARALLEL);
//		dsolver = new PardinusSolver(opt);
//		final PardinusBounds bounds = new PardinusBounds(model.bounds1(),model.bounds2());
//		final Formula formula = model.partition1().and(model.partition2());
//		Explorer<Solution> sols;
//
////		System.out.println("----- Solving decomposed -----");
//		sols = dsolver.solveAll(formula, bounds);
//		Solution sol;
//		int decomp_counter = 0;
////		while (sols.hasNextC()) {
////			sol = sols.nextC();
////
//////			System.out.print(sol.outcome().toString()+" " + decomp_counter + ": ");
////			if (sol.sat()) {
////				decomp_counter++;
//////				System.out.println(sol.instance().relationTuples());
////			} else {
//////				System.out.println();
////			}
////		}
//		Set<IntSet> decomp_syms = last;
//		dsolver.free();
//		last = null;
//
////		System.out.println("----- Solving in batch -----");
//
//		opt.setRunDecomposed(false);
//		PardinusSolver solver = new PardinusSolver(opt);
//		PardinusBounds mbounds = model.bounds1();
//		mbounds.merge(model.bounds2());
//		sol = solver.solve(formula, mbounds);
//		int batch_counter = 0;
////		System.out.print(sol.outcome().toString()+" " + batch_counter + ": ");
////		if (sol.sat()) {
////			batch_counter++;
//////			System.out.println(sol.instance().relationTuples());
////		} else {
//////			System.out.println();
////		}
//		Set<IntSet> batch_syms = last;
//		solver.free();
//
//		// if config is trivially unsat, then time symmetries are not found on partial problem
//		Assert.assertTrue(batch_syms.equals(decomp_syms) || (decomp_counter == 1 && batch_syms.size() == decomp_syms.size()+1));
//		Assert.assertEquals(batch_counter, Math.min(1,decomp_counter));
//
//	}

}
