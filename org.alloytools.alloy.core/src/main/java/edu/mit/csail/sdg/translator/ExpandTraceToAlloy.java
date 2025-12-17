package edu.mit.csail.sdg.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprBinary;
import edu.mit.csail.sdg.ast.ExprCall;
import edu.mit.csail.sdg.ast.ExprConstant;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprITE;
import edu.mit.csail.sdg.ast.ExprLet;
import edu.mit.csail.sdg.ast.ExprList;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;


public class ExpandTraceToAlloy extends VisitReturn<Expr> {

    private Map<ExprHasName,Map<Sig.Field,ExprVar>> trace_vars = new HashMap<>();
    private Expr                                    trace_var  = null;

    @Override
    public Expr visit(ExprBinary x) throws Err {
        if (x.op == ExprBinary.Op.JOIN && trace_vars.containsKey(x.left.deNOP())) {
            if (trace_var != null)
                throw new ErrorSyntax(x.pos, "Invalid trace var call.");
            trace_var = x.left.deNOP();
            Expr r = x.right.accept(this);
            trace_var = null;
            return r;
        }
        Expr l = x.left.accept(this);
        Expr r = x.right.accept(this);
        return x.op.make(x.pos, x.closingBracket, l, r);
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        List<Expr> cs = new ArrayList<>();
        for (Expr c : x.args)
            cs.add(c.accept(this));
        return ExprList.make(x.pos, x.closingBracket, x.op, cs);
    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        List<Expr> cs = new ArrayList<>();
        for (Expr c : x.args) {
            if (trace_vars.containsKey(c.deNOP())) {
                Sig tp = c.type().fold().get(0).get(0);
                for (Sig.Field trace_field : tp.getFields()) {
                    cs.add(trace_vars.get(c.deNOP()).get(trace_field));
                }
            } else
                cs.add(c.accept(this));
        }
        Func f = (Func) x.fun.accept(this);
        return ExprCall.make(x.pos, x.closingBracket, f, cs, x.extraWeight);
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        if (trace_var != null)
            throw new ErrorSyntax(x.pos, "Invalid constant inside trace projection.");
        return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        Expr l = x.left.accept(this);
        Expr r = x.right.accept(this);
        Expr c = x.cond.accept(this);
        return ExprITE.make(x.pos, c, l, r);
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        Expr e = x.expr.accept(this);
        Expr s = x.sub.accept(this);
        return ExprLet.make(x.pos, x.var, e, s);
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        List<Decl> ds = new ArrayList<>();
        for (Decl d : x.decls) {
            Sig tp = d.expr.type().fold().get(0).get(0);
            if (tp.isTrace != null) {
                for (Sig.Field trace_field : tp.getFields()) {
                    List<ExprHasName> nvs = new ArrayList<>();
                    for (ExprHasName trace_var : d.names) {
                        for (ExprHasName trace_field_var : trace_field.decl().names) {
                            ExprVar nv = ExprVar.make(trace_field_var.pos, trace_var.label + "_" + trace_field_var.label, trace_field.decl().expr.type());
                            nvs.add(nv);
                            trace_vars.computeIfAbsent(trace_var, xx -> new HashMap<>()).put(trace_field, nv);
                        }
                    }
                    ds.add(new Decl(trace_field.isPrivate, trace_field.decl().disjoint, trace_field.decl().disjoint2, trace_field.isVariable, nvs, trace_field.decl().expr));
                }
            } else {
                Expr e = d.expr.accept(this);
                ds.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.isVar, d.names, e));
            }
        }

        Expr d = x.dom.accept(this);
        Expr s = x.sub.accept(this);
        return x.op.make(x.pos, x.closingBracket, ds, d, s);
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        Expr s = x.sub.accept(this);
        return x.op.make(x.pos, s);
    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Sig x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Sig.Field x) throws Err {
        if (trace_var != null && trace_vars.get(trace_var).containsKey(x))
            return trace_vars.get(trace_var).get(x);
        return x;
    }

    @Override
    public Expr visit(Func x) throws Err {
        List<Decl> ds = new ArrayList<>();
        for (Decl d : x.decls) {
            Sig tp = d.expr.type().fold().get(0).get(0);
            if (tp.isTrace != null) {
                for (ExprHasName trace_var : d.names) {
                    for (Sig.Field trace_field : tp.getFields()) {
                        List<ExprHasName> nvs = new ArrayList<>();
                        for (ExprHasName trace_field_var : trace_field.decl().names) {
                            ExprVar nv = ExprVar.make(trace_field_var.pos, trace_var.label + "_" + trace_field_var.label, trace_field.decl().expr.type());
                            nvs.add(nv);
                            trace_vars.computeIfAbsent(trace_var, xx -> new HashMap<>()).put(trace_field, nv);
                        }
                        ds.add(new Decl(trace_field.isPrivate, trace_field.decl().disjoint, trace_field.decl().disjoint2, trace_field.isVariable, nvs, trace_field.decl().expr));
                    }
                }
            } else {
                Expr e = d.expr.accept(this);
                ds.add(new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.isVar, d.names, e));
            }
        }
        Expr r = x.returnDecl.accept(this);
        Expr b = x.getBody().accept(this);

        return new Func(x.pos, x.labelPos, x.label, ds, r, b);
    }

    @Override
    public Expr visit(Assert x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Macro macro) throws Err {
        return macro;
    }
}
