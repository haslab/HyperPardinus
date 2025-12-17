package kodkod.test.pardinus.temporal;

import kodkod.ast.*;
import kodkod.engine.ltl2fol.InvalidMutableExpressionException;
import kodkod.engine.ltl2fol.LTL2FOLTranslator;
import kodkod.engine.ltl2fol.TemporalTranslator;

import org.junit.Test;

import static org.junit.Assert.assertEquals;

import java.util.LinkedHashMap;

import org.junit.BeforeClass;

import static kodkod.engine.ltl2fol.TemporalTranslator.FIRST;
import static kodkod.engine.ltl2fol.TemporalTranslator.TRACE;
import static kodkod.engine.ltl2fol.TemporalTranslator.PREFIX;

/**
 * Tests whether the translation of PLTL formulas is done correctly.
 * 
 * As of Pardinus 1.1, traces are always assumed to be infinite.
 * 
 * Assumes past translation with {@link TemporalTranslator#ExplicitUnrolls} true.
 * 
 * @author Eduardo Pessoa, Nuno Macedo // [HASLab] decomposed model finding
 */
public class TemporalTranslatorTests {

	private static Relation Process = Relation.unary("Process");
	private static Relation toSend = Relation.binary_variable("toSend");
	private static Relation elected = Relation.unary_variable("elected");
	private static Relation naryRelation = Relation.variable("naryRelation", 4);

	private static Relation succ = Relation.binary("succ");

	private static Relation pfirst = Relation.unary("pfirst");
	private static Relation plast = Relation.unary("plast");
	private static Relation pord = Relation.binary_variable("pord");

	public TemporalTranslatorTests() {}
	
	/* Declarations */
	@Test
	public final void test() {
		Formula initial = (elected.eq(elected.prime()).not()).after();
		Formula result = elected.getExpansion().join(FIRST.join(TRACE)).eq(elected.getExpansion().join(FIRST.join(TRACE).join(TRACE))).not();
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	/* Declarations */
	@Test
	public final void declaration_one() {
		Formula initial = elected.in(Process);
		Formula result = elected.getExpansion().join(FIRST).in(Process);
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void declaration_two() {
		Formula initial = toSend.in(Process.product(Process));
		Formula result = toSend.getExpansion().join(FIRST).in(Process.product(Process));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void declaration_three() {
		Formula initial = naryRelation.in(Process.product(Process).product(Process).product(Process));
		Formula result = naryRelation.getExpansion().join(FIRST).in(Process.product(Process).product(Process).product(Process));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void declaration_totalFunction() {
		Formula initial = pord.function(pfirst, plast);
		try {
			((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString();
			assert(false);
		} catch (InvalidMutableExpressionException e) {
			assert(true);
		}
	}

	@Test
	public final void declaration_partialFunction() {
		Formula initial = pord.partialFunction(pfirst, plast);
		try {
			((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString();
			assert(false);
		} catch (InvalidMutableExpressionException e) {
			assert(true);
		}
	}

	@Test
	public final void declaration_normal_partialFunction() {
		Formula initial = succ.partialFunction(pfirst, plast);
		Formula result = succ.partialFunction(pfirst, plast);
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void declaration_normal_function() {
		Formula initial = succ.partialFunction(pfirst, plast);
		Formula result = succ.partialFunction(pfirst, plast);
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	/* Temporal */
	@Test
	public final void simple_post_init() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.prime().join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process));
		Formula result = (v.in(toSend.getExpansion().join(FIRST.join(TRACE)).join(v)).and(v.in(toSend.getExpansion().join(FIRST).join(v))).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_always() {
		Variable v = Variable.unary("p");
		Variable t = Variable.unary("t0");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Formula result = (v.in(toSend.getExpansion().join(t).join(v)).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_next() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).after();
		Formula result = (v.in(toSend.getExpansion().join(FIRST.join(TRACE)).join(v)).and(v.in(toSend.getExpansion().join(FIRST.join(TRACE)).join(v))).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void simple_prime() {
		Variable v = Variable.unary("p");
		Formula initial = (toSend.join(v).prime()).eq(toSend.join(v)).forAll(v.oneOf(Process));
		Formula result = (toSend.getExpansion().join(FIRST.join(TRACE)).join(v).eq(toSend.getExpansion().join(FIRST).join(v)).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void simple_double_prime() {
		Variable v = Variable.unary("p");
		Formula initial = (toSend.join(v).prime()).eq(toSend.prime().join(v).prime()).forAll(v.oneOf(Process));
		Formula result = (toSend.getExpansion().join(FIRST.join(TRACE)).join(v).eq(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE)).join(v)).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = v.in(toSend.getExpansion().join(t).join(v)).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_historically() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process))
				.historically();
		Variable t = Variable.unary("t0");
		Formula result = v.in(toSend.getExpansion().join(t).join(v)).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(PREFIX.transpose().reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_once() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).once();
		Variable t = Variable.unary("t0");
		Formula result = v.in(toSend.getExpansion().join(t).join(v)).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(PREFIX.transpose().reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void simple_previous() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).before();
		Formula result = FIRST.join(PREFIX.transpose()).some().and(v.in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose())).join(v)).and(v.in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose())).join(v))).forAll(v.oneOf(Process)));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_prime_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend)).always();
		Variable t = Variable.unary("t0");
		Formula result = (((v.join(toSend.getExpansion().join(t.join(TRACE))).eq(v.join(toSend.getExpansion().join(t))))).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());

	}

	@Test
	public final void simple_post_next_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend)).after().always();
		Variable t = Variable.unary("t0");
		Formula result = ((v.join(toSend.getExpansion().join(t.join(TRACE).join(TRACE))).eq(v.join(toSend.getExpansion().join(t.join(TRACE))))).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());

	}

	@Test
	public final void simple_post_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = (v.join(toSend.getExpansion().join(t.join(TRACE))).eq(v.join(toSend.getExpansion().join(t)))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void simple_post_next_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.join(toSend.prime()).eq(v.join(toSend).prime().prime()).after().eventually();
		Variable t = Variable.unary("t0");
		Formula result = ((v.join(toSend.getExpansion().join(t.join(TRACE).join(TRACE))).eq(v.join(toSend.getExpansion().join(t.join(TRACE).join(TRACE).join(TRACE)))))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void simple_post_next() {
		Formula initial = toSend.prime().eq(toSend).after();
		Formula result = (toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE)).eq(toSend.getExpansion().join(FIRST.join(TRACE))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_until() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).lone());
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f2 = Process.join(toSend.getExpansion().join(t1)).some().forAll(t1.oneOf(upTo(FIRST,t,false)));
		Formula f1 = Process.join(toSend.getExpansion().join(t)).lone().and(f2).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula result = f1;
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_since() {
		Formula initial = Process.join(toSend).some().since(Process.join(toSend).lone());
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f2 = Process.join(toSend.getExpansion().join(t1)).some().forAll(t1.oneOf(downTo(FIRST,t,false)));
		Formula f1 = Process.join(toSend.getExpansion().join(t)).lone().and(f2).forSome(t.oneOf(FIRST.join(PREFIX.transpose().reflexiveClosure())));
		Formula result = f1;
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	private Expression upTo(Expression t1, Expression t2, boolean inc2) {
		Formula c = t2.in(t1.join(PREFIX.reflexiveClosure()));
		Expression exp1 = PREFIX.reflexiveClosure();
		Expression exp2 = PREFIX.closure();
		Expression exp11 = TRACE.reflexiveClosure();
		Expression exp12 = TRACE.closure();
		Expression e1 = (t1.join(exp1)).intersection(t2.join(exp2.transpose()));
		Expression e21 = (t1.join(exp11)).intersection(t2.join(exp12.transpose()));
		Expression e22 = (t2.join(exp1)).intersection(t1.join(exp2.transpose()));
		Expression e2 = e21.difference(e22);
		Expression e = c.thenElse(e1, e2);
		if (inc2) e = e.union(t2); 
		return e;
	}
	
	private Expression downTo(Expression t1, Expression t2, boolean inc2) {
		Expression exp1 = PREFIX.reflexiveClosure();
		Expression exp2 = PREFIX.closure();
		Expression e1 = (t1.join(exp1.transpose())).intersection(t2.join(exp2));
		Expression e = e1;
		if (inc2) e = e.union(t2); 
		return e;
	}

	@Test
	public final void simple_release() {
		Formula initial = Process.join(toSend).some().releases(Process.join(toSend).lone());
		Variable t = Variable.unary("t1");
		Variable t1 = Variable.unary("t2");
		Variable t2 = Variable.unary("t0");
		Formula f2 = Process.join(toSend.getExpansion().join(t1)).lone().forAll(t1.oneOf(upTo(FIRST,t,true)));
		Formula f1 = Process.join(toSend.getExpansion().join(t)).some().and(f2).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula f3 = Process.join(toSend.getExpansion().join(t2)).lone().forAll(t2.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula result = ((f3)).or(f1);
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_release_post() {
		Variable v = Variable.unary("p");
		Formula initial = toSend.join(v).eq(toSend.join(v)).releases(Process.join(toSend.prime()).lone()).forAll(v.oneOf(Process));
		Variable t = Variable.unary("t1");
		Variable t1 = Variable.unary("t2");
		Variable t2 = Variable.unary("t0");
		Formula f2 = (Process.join(toSend.getExpansion().join(t1.join(TRACE))).lone()).forAll(t1.oneOf(upTo(FIRST,t,true)));
		Formula f1 = toSend.getExpansion().join(t).join(v).eq(toSend.getExpansion().join(t).join(v)).and(f2).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula f3 = Process.join(toSend.getExpansion().join(t2.join(TRACE))).lone().forAll(t2.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		Formula result = ((f3)).or(f1).forAll(v.oneOf(Process));

		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	/* Out of the root */
	@Test
	public final void simple_always_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).always().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = (((v.in(toSend.getExpansion().join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.reflexiveClosure())))).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_always_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).always().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = ((v.in(toSend.getExpansion().join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.reflexiveClosure())))).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_once_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).once().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = ((v.in(toSend.getExpansion().join(t1).join(v))).forSome(t1.oneOf(t.join(PREFIX.transpose().reflexiveClosure()))).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_historically_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).historically().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula result = (v.in(toSend.getExpansion().join(t1).join(v))).forAll(t1.oneOf(t.join(PREFIX.transpose().reflexiveClosure()))).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_next_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).after().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Formula result = (v.in(toSend.getExpansion().join(t.join(TRACE)).join(v)).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_previous_always() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).before().and(v.in(toSend.join(v))).forAll(v.oneOf(Process)).always();
		Variable t = Variable.unary("t0");
		Formula result = ((t.join(PREFIX.transpose()).some().and(v.in(toSend.getExpansion().join(t.join(PREFIX.transpose())).join(v)))).and(v.in(toSend.getExpansion().join(t).join(v))).forAll(v.oneOf(Process)).forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_previous_always_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).before().and(v.in(toSend.join(v)).always().and(v.in(toSend.join(v)))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f1 = t.join(PREFIX.transpose()).some().and(v.in(toSend.getExpansion().join(t.join(PREFIX.transpose())).join(v)));
		Formula f2 = ((v.in(toSend.getExpansion().join(t1).join(v))).forAll(t1.oneOf(t.join(TRACE.reflexiveClosure()))));
		Formula result = ((f1.and(f2.and(v.in(toSend.getExpansion().join(t).join(v))))).forAll(v.oneOf(Process))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_next_eventually_eventually() {
		Variable v = Variable.unary("p");
		Formula initial = v.in(toSend.join(v)).after().and(v.in(toSend.join(v)).eventually().and(v.in(toSend.join(v)))).forAll(v.oneOf(Process)).eventually();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Formula f1 = (v.in(toSend.getExpansion().join(t.join(TRACE)).join(v)));
		Formula f2 = (v.in(toSend.getExpansion().join(t1).join(v))).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = ((f1.and(f2.and(v.in(toSend.getExpansion().join(t).join(v))))).forAll(v.oneOf(Process))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	
	@Test
	public final void simple_until_always() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).lone()).always();
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Variable t2 = Variable.unary("t2");
		Formula f2 = Process.join(toSend.getExpansion().join(t2)).some().forAll(t2.oneOf(upTo(t,t1,false)));
		Formula f1 = Process.join(toSend.getExpansion().join(t1)).lone().and(f2).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = (f1.forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_always_until_eventually() {
		Formula initial = Process.join(toSend).some().always().until(Process.join(toSend).lone()).eventually();

		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Variable t2 = Variable.unary("t2");
		Variable t3 = Variable.unary("t3");
		Formula f2 = ((Process.join(toSend.getExpansion().join(t3)).some().forAll(t3.oneOf(t2.join(TRACE.reflexiveClosure()))))).forAll(t2.oneOf(upTo(t,t1,false)));
		Formula f1 = Process.join(toSend.getExpansion().join(t1)).lone().and(f2).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = f1.forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void simple_release_always() {
		Formula initial = Process.join(toSend).some().releases(Process.join(toSend).lone()).always();
		Variable t = Variable.unary("t2");
		Variable t1 = Variable.unary("t3");
		Variable t2 = Variable.unary("t1");
		Variable t3 = Variable.unary("t0");
		Formula f2 = Process.join(toSend.getExpansion().join(t1)).lone().forAll(t1.oneOf(upTo(t3,t,true)));
		Formula f1 = Process.join(toSend.getExpansion().join(t)).some().and(f2).forSome(t.oneOf(t3.join(TRACE.reflexiveClosure())));
		Formula f3 = Process.join(toSend.getExpansion().join(t2)).lone().forAll(t2.oneOf(t3.join(TRACE.reflexiveClosure())));
		Formula result = (((f3)).or(f1).forAll(t3.oneOf(FIRST.join(TRACE.reflexiveClosure()))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());	}

	@Test
	public final void simple_until1_always() {
		Formula initial = Process.join(toSend).some().until(Process.join(toSend).prime().lone()).always().and(toSend.one());
		Variable t = Variable.unary("t0");
		Variable t1 = Variable.unary("t1");
		Variable t2 = Variable.unary("t2");
		Formula f2 = Process.join(toSend.getExpansion().join(t2)).some().forAll(t2.oneOf(upTo(t,t1,false)));
		Formula f1 = ((Process.join(toSend.getExpansion().join(t1.join(TRACE))).lone()).and(f2)).forSome(t1.oneOf(t.join(TRACE.reflexiveClosure())));
		Formula result = ((f1.forAll(t.oneOf(FIRST.join(TRACE.reflexiveClosure())))).and(toSend.getExpansion().join(FIRST).one()));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());	
	}

	/* Prime, next and previous */
	@Test
	public final void nested_primes() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = (((toSend.getExpansion().join(t.join(TRACE)).join(toSend.getExpansion().join(t.join(TRACE).join(TRACE)))).in(toSend.getExpansion().join(t)))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void nested_primes2() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).and(toSend.prime().prime().prime().in(toSend)).eventually();
		Variable t = Variable.unary("t0");
		Formula result = ((toSend.getExpansion().join(t.join(TRACE)).join(toSend.getExpansion().join(t.join(TRACE).join(TRACE))).in(toSend.getExpansion().join(t))).and(toSend.getExpansion().join(t.join(TRACE).join(TRACE).join(TRACE)).in(toSend.getExpansion().join(t)))).forSome(t.oneOf(FIRST.join(TRACE.reflexiveClosure())));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}

	@Test
	public final void nested_primes3() {
		Formula initial = ((toSend.join(toSend.prime())).prime().in(toSend)).and(toSend.prime().prime().prime().in(toSend));
		Formula result = ((toSend.getExpansion().join(FIRST.join(TRACE)).join(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE))).in(toSend.getExpansion().join(FIRST))).and(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST))));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void nested_next() {
		Formula initial = (toSend.in(toSend).after().after()).and(toSend.in(toSend).after()).after();
		Formula f1 = (toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE).join(TRACE))));
		Formula f2 = (toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE))));
		Formula result = (f1.and(f2));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void nested_next_prime() {
		Formula initial = (toSend.in(toSend).after().after()).and(toSend.in(toSend.prime()).after()).after();
		Formula f1 = ((toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE).join(TRACE)))));
		Formula f2 = (toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(TRACE).join(TRACE).join(TRACE))));
		Formula result = (f1.and(f2));
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void nested_previous() {
		Formula initial = (toSend.in(toSend).before().before()).and(toSend.in(toSend).before()).before();
		Formula f1 = FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).some().and(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).join(PREFIX.transpose()).some().and(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).join(PREFIX.transpose())).in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).join(PREFIX.transpose())))));
		Formula f2 = FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).some().and(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose())).in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()))));
		Formula result = FIRST.join(PREFIX.transpose()).some().and(f1.and(f2));		
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void nested_previous_next() {
		Formula initial = (toSend.in(toSend)).after().before();
		Formula f1 = (toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(TRACE))));
		Formula result = FIRST.join(PREFIX.transpose()).some().and(f1);		
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void nested_previous_prime() {
		Formula initial = (toSend.in(toSend.prime())).before();
		Formula f1 = (toSend.getExpansion().join(FIRST.join(PREFIX.transpose())).in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(TRACE))));
		Formula result = FIRST.join(PREFIX.transpose()).some().and(f1);		
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
	
	@Test
	public final void nested_previous_next_prime() {
		Formula initial = ((toSend.prime().prime().in(toSend.prime()).after()).and((toSend.prime().prime().in(toSend.prime()).before()))).before();
		Formula f1 = (toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(TRACE).join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(TRACE).join(TRACE))));
		Formula f2 = FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).some().and(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).join(TRACE).join(TRACE)).in(toSend.getExpansion().join(FIRST.join(PREFIX.transpose()).join(PREFIX.transpose()).join(TRACE))));
		Formula result = FIRST.join(PREFIX.transpose()).some().and(f1.and(f2));		
		assertEquals(result.toString(), ((BinaryFormula)LTL2FOLTranslator.translate(initial,0,false,new LinkedHashMap<Formula,Formula>())).right().toString());
	}
}
