package edu.mit.csail.sdg.translator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.Err;
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
import edu.mit.csail.sdg.ast.ExprList.Op;
import edu.mit.csail.sdg.ast.ExprQt;
import edu.mit.csail.sdg.ast.ExprUnary;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.VisitReturn;
import edu.mit.csail.sdg.parser.Macro;


public class FlattenFormula extends VisitReturn<Expr> {

    Map<ExprHasName,Expr> binding = new HashMap<>();
    boolean               negated = false;

    @Override
    public Expr visit(ExprBinary x) throws Err {
        if (x.op == ExprBinary.Op.IMPLIES)
            return ExprBinary.Op.OR.make(x.pos, x.closingBracket, x.left.not(), x.right).accept(this);
        if (x.op == ExprBinary.Op.IFF) {
            Expr l = ExprBinary.Op.IMPLIES.make(x.pos, x.closingBracket, x.left, x.right);
            Expr r = ExprBinary.Op.IMPLIES.make(x.pos, x.closingBracket, x.right, x.left);
            return ExprBinary.Op.AND.make(x.pos, x.closingBracket, l, r).accept(this);
        }

        Expr res;
        List<Expr> args = new ArrayList<Expr>();
        if (x.op == ExprBinary.Op.AND || x.op == ExprBinary.Op.OR) {
            Expr l = x.left.accept(this);
            Expr r = x.right.accept(this);
            if (l instanceof ExprList && ((ExprList) l).op == Op.AND && x.op == ExprBinary.Op.AND)
                args.addAll(((ExprList) l).args);
            else if (l instanceof ExprList && ((ExprList) l).op == Op.OR && x.op == ExprBinary.Op.OR)
                args.addAll(((ExprList) l).args);
            else
                args.add(l);
            if (r instanceof ExprList && ((ExprList) r).op == Op.AND && x.op == ExprBinary.Op.AND)
                args.addAll(((ExprList) r).args);
            else if (r instanceof ExprList && ((ExprList) r).op == Op.OR && x.op == ExprBinary.Op.OR)
                args.addAll(((ExprList) r).args);
            else
                args.add(r);
            ExprList.Op o = ((x.op == ExprBinary.Op.AND && !negated) || (x.op == ExprBinary.Op.OR && negated)) ? ExprList.Op.AND : ExprList.Op.OR;
            res = ExprList.make(x.pos, x.closingBracket, o, args);
        } else if (negated) {
            negated = !negated;
            Expr l = x.left.accept(this);
            Expr r = x.right.accept(this);
            res = x.op.make(x.pos, x.closingBracket, l, r).not();
            negated = !negated;
        } else {
            Expr l = x.left.accept(this);
            Expr r = x.right.accept(this);
            res = x.op.make(x.pos, x.closingBracket, l, r);
        }
        return res;
    }

    @Override
    public Expr visit(ExprList x) throws Err {
        List<Expr> cs = new ArrayList<>();
        for (Expr c : x.args) {
            if (x.op == Op.AND || x.op == Op.OR) {
                Expr c2 = c.accept(this);
                if (c2 instanceof ExprList && ((((ExprList) c2).op == Op.AND && !negated) || (((ExprList) c2).op == Op.OR && negated)) && x.op == Op.AND)
                    cs.addAll(((ExprList) c2).args);
                else if (c2 instanceof ExprList && ((((ExprList) c2).op == Op.OR && !negated) || (((ExprList) c2).op == Op.AND && negated)) && x.op == Op.OR)
                    cs.addAll(((ExprList) c2).args);
                else
                    cs.add(c2);
            } else {
                negated = !negated;
                Expr c2 = c.accept(this);
                cs.add(c2);
                negated = !negated;
            }
        }
        if (x.op == Op.AND || x.op == Op.OR) {
            ExprList.Op o = ((x.op == ExprList.Op.AND && !negated) || (x.op == ExprList.Op.OR && negated)) ? ExprList.Op.AND : ExprList.Op.OR;
            return ExprList.make(x.pos, x.closingBracket, o, cs);
        } else if (negated) {
            return ExprList.make(x.pos, x.closingBracket, x.op, cs).not();
        } else {
            return ExprList.make(x.pos, x.closingBracket, x.op, cs);
        }

    }

    @Override
    public Expr visit(ExprCall x) throws Err {
        int i = 0;
        boolean pre = negated;
        negated = false;
        for (Decl d : x.fun.decls) {
            for (ExprHasName name : d.names) {
                binding.put(name, x.args.get(i).accept(this));
                i++;
            }
        }
        negated = pre;
        Expr res = x.fun.getBody().accept(this);

        for (Decl d : x.fun.decls)
            for (ExprHasName name : d.names)
                binding.remove(name);

        return res;
    }

    @Override
    public Expr visit(ExprConstant x) throws Err {
        if (negated)
            return x.not();
        else
            return x;
    }

    @Override
    public Expr visit(ExprITE x) throws Err {
        if (negated) {
            negated = !negated;
            Expr l = x.left.accept(this);
            Expr r = x.left.accept(this);
            Expr c = x.cond.accept(this);
            negated = !negated;
            return ExprITE.make(x.pos, c, l, r).not();
        } else {
            Expr l = x.left.accept(this);
            Expr r = x.left.accept(this);
            Expr c = x.cond.accept(this);
            return ExprITE.make(x.pos, c, l, r);
        }
    }

    @Override
    public Expr visit(ExprLet x) throws Err {
        if (negated) {
            negated = !negated;
            Expr e = x.expr.accept(this);
            Expr s = x.sub.accept(this);
            negated = !negated;
            return ExprLet.make(x.pos, x.var, e, s).not();
        } else {
            Expr e = x.expr.accept(this);
            Expr s = x.sub.accept(this);
            return ExprLet.make(x.pos, x.var, e, s);
        }
    }

    @Override
    public Expr visit(ExprQt x) throws Err {
        List<Decl> ds = new ArrayList<Decl>();
        boolean pre_neg = negated;
        negated = false;
        for (Decl dc : x.decls) {
            Expr dexpr = dc.expr.accept(this);
            ds.add(new Decl(dc.isPrivate, dc.disjoint, dc.disjoint2, dc.isVar, dc.names, dexpr));
        }
        negated = pre_neg;

        if (x.op == ExprQt.Op.ALL || x.op == ExprQt.Op.SOME) {
            Expr d = x.dom.accept(this);
            Expr s = x.sub.accept(this);
            ExprQt.Op o = ((x.op == ExprQt.Op.ALL && !negated) || (x.op == ExprQt.Op.SOME && negated)) ? ExprQt.Op.ALL : ExprQt.Op.SOME;
            return o.make(x.pos, x.closingBracket, ds, d, s);
        } else if (negated) {
            negated = !negated;
            Expr d = x.dom.accept(this);
            Expr s = x.sub.accept(this);
            negated = !negated;
            return x.op.make(x.pos, x.closingBracket, ds, d, s).not();
        } else {
            Expr d = x.dom.accept(this);
            Expr s = x.sub.accept(this);
            return x.op.make(x.pos, x.closingBracket, ds, d, s);
        }
    }

    @Override
    public Expr visit(ExprUnary x) throws Err {
        if (x.op == ExprUnary.Op.NOOP)
            return x.sub.accept(this);
        if (x.op == ExprUnary.Op.NOT) {
            negated = !negated;
            Expr res = x.sub.accept(this);
            negated = !negated;
            return res;
        } else if (x.op == ExprUnary.Op.ALWAYS || x.op == ExprUnary.Op.EVENTUALLY) {
            Expr res = x.sub.accept(this);
            ExprUnary.Op o = ((x.op == ExprUnary.Op.ALWAYS && !negated) || (x.op == ExprUnary.Op.EVENTUALLY && negated)) ? ExprUnary.Op.ALWAYS : ExprUnary.Op.EVENTUALLY;
            return o.make(x.pos, res);
        } else if (x.op == ExprUnary.Op.HISTORICALLY || x.op == ExprUnary.Op.ONCE) {
            Expr res = x.sub.accept(this);
            ExprUnary.Op o = ((x.op == ExprUnary.Op.HISTORICALLY && !negated) || (x.op == ExprUnary.Op.ONCE && negated)) ? ExprUnary.Op.HISTORICALLY : ExprUnary.Op.ONCE;
            return o.make(x.pos, res);
        } else if (negated) {
            negated = !negated;
            Expr res = x.op.make(x.pos, x.sub.accept(this)).not();
            negated = !negated;
            return res;
        } else {
            return x.op.make(x.pos, x.sub.accept(this));
        }
    }

    @Override
    public Expr visit(ExprVar x) throws Err {
        return binding.getOrDefault(x, x);
    }

    @Override
    public Expr visit(Sig x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Sig.Field x) throws Err {
        return x;
    }

    @Override
    public Expr visit(Func x) throws Err {
        throw new RuntimeException("Should have been flattened.");
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
