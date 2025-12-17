package edu.mit.csail.sdg.alloy4;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.junit.Test;

import edu.mit.csail.sdg.ast.Attr;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Sig.Field;
import edu.mit.csail.sdg.ast.Sig.PrimSig;
import edu.mit.csail.sdg.translator.FlattenFormula;
import edu.mit.csail.sdg.translator.TraceFormulas;


public class TraceFormulasTest {

    final Sig   sig_reg   = new PrimSig("A");
    final Sig   sig_trace = new PrimSig("S", Attr.TRACE);
    final Field field_r   = sig_trace.addField("r", sig_reg);


    @Test
    public void testAllBasic1() {
        Decl d = sig_trace.oneOf("s");
        Expr f = ((d.get().join(field_r)).some()).implies(sig_reg.some()).forAll(d);

        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals((ExprConstant.FALSE.or(sig_reg.some())).forAll(d).toString(), res.toString());
        assertEquals((d.get().join(field_r)).some().toString(), x.get(d.get()).get(0).toString());
    }

    @Test
    public void testAllBasic2() {
        Decl d = sig_trace.oneOf("s");
        Expr f = ((d.get().join(field_r)).some()).and(sig_reg.some()).forAll(d);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals((ExprConstant.FALSE).forAll(d).toString(), res.toString());
        assertEquals(((d.get().join(field_r)).some().not()).or(sig_reg.some().not()).toString(), x.get(d.get()).get(0).toString());
    }

    @Test
    public void testSomeBasic1() {
        Decl d = sig_trace.oneOf("s");
        Expr f = (((d.get().join(field_r)).some()).and(sig_reg.some())).forSome(d);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals(ExprList.make(null, null, ExprList.Op.AND, Arrays.asList(sig_reg.some())).forSome(d).toString(), res.toString());
        assertEquals(((d.get().join(field_r)).some()).toString(), x.get(d.get()).get(0).toString());
    }

    @Test
    public void testSomeBasic2() {
        Decl d = sig_trace.oneOf("s");
        Expr f = (((d.get().join(field_r)).some()).implies(sig_reg.some())).forSome(d);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals(ExprConstant.TRUE.forSome(d).toString(), res.toString());
        assertEquals(((d.get().join(field_r)).some().not()).or(sig_reg.some()).toString(), x.get(d.get()).get(0).toString());
    }

    @Test
    public void testAllMult1() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = ((d1.get().join(field_r)).equal((d2.get().join(field_r)))).implies(sig_reg.some()).forAll(d1).forAll(d2);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals(((d1.get().join(field_r)).equal((d2.get().join(field_r)))).not().or(sig_reg.some()).forAll(d1).forAll(d2).toString(), res.toString());
        assertNull(x.get(d1.get()));
        assertNull(x.get(d2.get()));
    }

    @Test
    public void testAllMult2() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = ((d1.get().join(field_r)).some()).implies(sig_reg.some()).forAll(d1).forAll(d2);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals((ExprConstant.FALSE).or(sig_reg.some()).forAll(d1).forAll(d2).toString(), res.toString());
        assertEquals(((d1.get().join(field_r)).some()).toString(), x.get(d1.get()).get(0).toString());
        assertNull(x.get(d2.get()));
    }

    @Test
    public void testAllMult3() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = ((d1.get().join(field_r)).some()).implies(sig_reg.some()).forAll(d1, d2);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals((ExprConstant.FALSE).or(sig_reg.some()).forAll(d1, d2).toString(), res.toString());
        assertEquals(((d1.get().join(field_r)).some()).toString(), x.get(d1.get()).get(0).toString());
        assertNull(x.get(d2.get()));
    }

    @Test
    public void testAllMult4() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = ((d1.get().join(field_r)).some().and((d2.get().join(field_r)).some())).implies(sig_reg.some()).forAll(d1, d2);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals(ExprConstant.FALSE.or(sig_reg.some()).forAll(d1, d2).toString(), res.toString());
        assertEquals(((d1.get().join(field_r)).some()).toString(), x.get(d1.get()).get(0).toString());
        assertEquals(((d2.get().join(field_r)).some()).toString(), x.get(d2.get()).get(0).toString());
    }

    @Test
    public void testAllMult5() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = ((d1.get().join(field_r)).some().or((d2.get().join(field_r)).some())).implies(sig_reg.some()).forAll(d1, d2);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals(((d1.get().join(field_r)).some().not().and((d2.get().join(field_r)).some().not())).or(sig_reg.some()).forAll(d1, d2).toString(), res.toString());
        assertNull(x.get(d1.get()));
        assertNull(x.get(d2.get()));
    }

    @Test
    public void testSomeMult1() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = ((d1.get().join(field_r)).some().and((d2.get().join(field_r)).some())).and(sig_reg.some()).forSome(d1, d2);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals((ExprConstant.TRUE.and(sig_reg.some())).forSome(d1, d2).toString(), res.toString());
        assertEquals(((d1.get().join(field_r)).some()).toString(), x.get(d1.get()).get(0).toString());
        assertEquals(((d2.get().join(field_r)).some()).toString(), x.get(d2.get()).get(0).toString());

    }

    @Test
    public void testAllNested1() {
        Decl d1 = sig_trace.oneOf("s1");
        Decl d2 = sig_trace.oneOf("s2");
        Expr f = d1.get().join(field_r).some().implies((d2.get().join(field_r)).some().implies(sig_reg.some()).forAll(d2)).forAll(d1);
        TraceFormulas tr = new TraceFormulas();
        Expr res = (new FlattenFormula()).visitThis(f).accept(tr);
        Map<ExprHasName,List<Expr>> x = tr.extracts;
        assertEquals(ExprConstant.FALSE.or(ExprConstant.FALSE.or(sig_reg.some()).forAll(d2)).forAll(d1).toString(), res.toString());
        assertEquals(((d1.get().join(field_r)).some()).toString(), x.get(d1.get()).get(0).toString());
        assertEquals(((d2.get().join(field_r)).some()).toString(), x.get(d2.get()).get(0).toString());
    }
}
