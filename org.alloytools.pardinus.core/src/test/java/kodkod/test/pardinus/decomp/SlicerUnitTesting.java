package kodkod.test.pardinus.decomp;

import static org.junit.Assert.assertEquals;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.AbstractReporter;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.decomp.DecompFormulaSlicer;
import kodkod.instance.Bounds;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import org.junit.BeforeClass;
import org.junit.Test;

/**
 * Tests whether the automatic formula slicing between conjuncts containing
 * partial and remainder bounds is correct.
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 */
public class SlicerUnitTesting {

	private static Relation Process = Relation.unary("Process");
	private static Relation toSend = Relation.binary_variable("toSend");
	private static Relation elected = Relation.unary_variable("elected");

	private static Relation succ = Relation.binary("succ");

	private static Relation pfirst = Relation.unary("pfirst");
	private static Relation plast = Relation.unary("plast");
	private static Relation pord = Relation.binary_variable("pord");
	private static Relation tord = Relation.binary_variable("tord");

	private static Relation succ1 = Relation.binary("succ1");
	private static Relation succ2 = Relation.binary("succ2");

	private static PardinusBounds bounds;
	
	@BeforeClass
	public static void doBounds() {
		List<Object> atoms = new ArrayList<Object>();
		for (int i = 0; i < 10; i++)
			atoms.add("A" + i);
		Universe u = new Universe(atoms);
		PardinusBounds bounds1 = new PardinusBounds(u);
		PardinusBounds bounds2 = new PardinusBounds(u);
		bounds1.bound(Process, u.factory().allOf(1));
		bounds2.bound(toSend, u.factory().allOf(2));
		bounds2.bound(elected, u.factory().allOf(1));
		bounds1.bound(succ, u.factory().allOf(2));
		bounds1.bound(pfirst, u.factory().allOf(1));
		bounds1.bound(plast, u.factory().allOf(1));
		bounds1.bound(pord, u.factory().allOf(2));
		bounds1.bound(tord, u.factory().allOf(2));
		bounds2.bound(succ1, u.factory().allOf(2));
		bounds2.bound(succ2, u.factory().allOf(2));
		bounds = new PardinusBounds(bounds1, bounds2);
	}
	
	@Test
	public final void test1() {
		Formula succFunction = tord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = Formula.and(new Formula[] { localFormula2, succFunction, var4, var5, initial2 });

		String resultDynamic = Formula.and(new Formula[] { var5, initial2 }).toString();
		String resultStatic = Formula.and(new Formula[] { localFormula2, succFunction, var4 }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
	}

	@Test
	public final void test2() {
		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Formula localFormula1 = localFormula2.and(var4.and(var5));

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = Formula.and(new Formula[] { localFormula1, initial2 });

		String resultDynamic = Formula.and(new Formula[] { var5, initial2 }).toString();
		String resultStatic = Formula.and(new Formula[] { localFormula2, var4 }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}
	
	@Test
	public final void test3() {
		Formula succFunction = pord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Formula localFormula1 = localFormula2.and(var4.and(var5.and(succFunction)));

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = Formula.and(new Formula[] { localFormula1, initial2 });

		String resultDynamic = Formula.and(new Formula[] { var5, initial2 }).toString();
		String resultStatic = Formula.and(new Formula[] { localFormula2, var4, succFunction }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}

	@Test
	public final void test4() {
		Formula succFunction = pord.partialFunction(pfirst, plast);

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);

		Formula localFormula1 = Formula.and(localFormula2, var4, var5, succFunction);

		Variable var3 = Variable.unary("p");
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = Formula.and(new Formula[] { localFormula1, initial2 });

		String resultDynamic = Formula.and(new Formula[] { var5, initial2 }).toString();
		String resultStatic = Formula.and(new Formula[] { localFormula2, var4, succFunction }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}

	@Test
	public final void test5() {
		Formula var1 = succ1.in(Process.product(Process)).implies(
				succ2.in(Process.product(Process)).and(succ.in(Process.product(Process))));
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();
		Formula var12 = succ2.in(Process.product(Process));
		Formula third = Formula.and(var1, var12, initial);// second.and(var13);
		// -------------

		Formula var11 = succ2.in(Process.product(Process));
		Formula third1 = var11.and(third);// second.and(var13);

		// ----------------

		Formula succFunction = pord.partialFunction(pfirst, plast);
		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = Formula.and(new Formula[] { third1, localFormula2, succFunction, var4, var5, initial2 });

		String resultDynamic = Formula.and(new Formula[] { var11, var1, var12, initial, var5, initial2 }).toString();
		String resultStatic = Formula.and(new Formula[] { localFormula2, succFunction, var4 }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}

	@Test
	public final void test6() {
		Formula var1 = succ1.in(Process.product(Process)).implies(
				succ2.in(Process.product(Process)).and(succ.in(Process.product(Process))));
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();
		Formula var12 = succ2.in(Process.product(Process));
		Formula third = Formula.and(var1, var12, initial);// second.and(var13);
		// -------------

		Formula var11 = succ2.in(Process.product(Process));
		Formula third1 = var11.and(third);// second.and(var13);

		// ----------------

		Formula var5 = elected.in(Process);
		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);
		Formula var6 = var5.and(var4.and(localFormula2));

		// ----------------
		Formula succFunction = pord.partialFunction(pfirst, plast);
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = Formula.and(new Formula[] { third1, var6, succFunction, initial2 });

		String resultDynamic = Formula.and(new Formula[] { var11, var1, var12, initial, var5, initial2 }).toString();
		String resultStatic = Formula.and(new Formula[] { var4, localFormula2, succFunction }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}

	@Test
	public final void test7() {
		Formula var1 = succ1.in(Process.product(Process));
		Variable var3 = Variable.unary("p");
		Formula initial = toSend.join(var3).eq(toSend.join(var3)).until(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();
		Formula first = initial.and(var1);

		Formula var12 = succ2.in(Process.product(Process));

		// -------------
		Formula var13 = succ2.in(Process.product(Process));
		Formula third = Formula.and(new Formula[] { var13, var12, first });
		// -------------

		Formula var11 = succ2.in(Process.product(Process));
		Formula third1 = var11.and(third);

		// ----------------

		Formula succFunction = pord.partialFunction(pfirst, plast);
		Formula var5 = elected.in(Process);

		Formula two = Formula.and(new Formula[] { succFunction, var5, third1 });

		Formula var4 = succ.in(Process.product(Process));
		Formula localFormula2 = pord.totalOrder(Process, pfirst, plast);
		Formula initial2 = toSend.join(var3).eq(toSend.join(var3)).releases(Process.join(toSend.prime()).lone())
				.forAll(var3.oneOf(Process)).after();

		Formula total = initial2.and(localFormula2.and(var4)).and(two);

		String resultDynamic = Formula.and(new Formula[] { initial2, var5, var11, var13, var12, initial, var1 }).toString();
		String resultStatic = Formula.and(new Formula[] { localFormula2, var4, succFunction }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}
	
	@Test
	public final void testOneConjunct() {
		Formula var1 = succ1.in(Process.product(Process));

		Formula total = var1;

		String resultDynamic = Formula.and(new Formula[] { var1 }).toString();
		String resultStatic = Formula.and(new Formula[] { }).toString();

		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(total, bounds);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", resultDynamic, dynamicRel.toString());
		assertEquals("incorrect partial partition", resultStatic, staticRel.toString());
	}
	
	Bounds subj1 = null;
	Formula subj2 = null;
	
	@Test
	public final void testTrivialIntegrated() {
		int n = 3;
		Relation a = Relation.unary("a");
		Relation b = Relation.unary("b");
		Relation c = Relation.unary("c");

		Object[] atoms = new Object[n];
		for (int i = 0; i < n; i++)
			atoms[i] = "A" + i;

		Universe uni = new Universe(atoms);
		TupleFactory f = uni.factory();
		TupleSet las = f.range(f.tuple("A0"), f.tuple("A0"));
		TupleSet as = f.range(f.tuple("A0"), f.tuple("A" + (n - 1)));

		PardinusBounds bounds1 = new PardinusBounds(uni);
		PardinusBounds bounds2 = new PardinusBounds(uni);
		bounds1.bound(a, las, as);
		bounds1.bound(b, las, as);
		bounds2.bound(c, las, as);
		PardinusBounds bounds = new PardinusBounds(bounds1, bounds2);
		Formula formula = a.eq(Expression.UNIV).and(a.in(b)); // all remainder trivial

		
		ExtendedOptions opt = new ExtendedOptions();
		
		opt.setRunDecomposed(true);
		opt.setReporter(new AbstractReporter() {
			
			@Override
			public void translatingToBoolean(Formula formula, Bounds bounds) {
				subj1 = bounds; subj2 = formula;
			}
		});
		
		PardinusSolver dsolver = new PardinusSolver(opt);
		
		Iterator<Solution> sols = dsolver.solveAll(formula, bounds);
		sols.next();
		
		// (!(a = a_1) or !(b = b_1) or !(c = c_1))
		Relation a_t = null, b_t = null, c_t = null;
		for (Relation r : subj1.relations())
			if (r.toString().length()<3) {}
			else if (r.toString().substring(0, 2).equals("a_"))
				a_t = r;
			else if (r.toString().substring(0, 2).equals("b_"))
				b_t = r;
			else if (r.toString().substring(0, 2).equals("c_"))
				c_t = r;
		Formula form = Formula.or(a.eq(a_t).not(),b.eq(b_t).not(),c.eq(c_t).not());
		
		
		Entry<Formula, Formula> entry = DecompFormulaSlicer.slice(form, (PardinusBounds) subj1);
		Formula dynamicRel = entry.getValue();
		Formula staticRel = entry.getKey();
		assertEquals("incorrect remainder partition", form.toString(), dynamicRel.toString());
		assertEquals("incorrect partial partition", Formula.TRUE.toString(), staticRel.toString());
	}

	public static void p(String s) {
		System.out.println(s);
	}
}
