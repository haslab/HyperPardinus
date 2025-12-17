package kodkod.ast;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.Multiplicity;

public class MixedMult extends Multiplicities {
	public final Multiplicities left, right;
	
	public MixedMult(Multiplicities left, Multiplicities right) {
		super(left.arity, Multiplicity.SET, false);
		assert left.arity == right.arity;
		this.left = left;
		this.right = right;
	}
	
	@Override
	protected List<Expression> domains() {
		List<Expression> l = new ArrayList<Expression>();
		l.addAll(left.domains());
		l.addAll(right.domains());
		return l;
	}
	
	@Override
	public void replace(Expression e1, Expression e2) {
		left.replace(e1, e2);
		right.replace(e1, e2);
	}
	
	@Override
	public Expression expr() {
		return left.expr().intersection(right.expr());
	}

	
	@Override
	public Multiplicities mergeMults(Multiplicities other) {
		return new MixedMult(this, other);
	}

}