package kodkod.ast;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.operator.Multiplicity;

public class ArrowMult extends Multiplicities {
	public final Multiplicities left, right;
	public ArrowMult(Multiplicities left, Multiplicities right, Multiplicity mult) {
		this(left, right, mult, false);
	}
	
	public ArrowMult(Multiplicities left, Multiplicities right, Multiplicity mult, boolean exact) {
		super(left.arity + right.arity, mult, exact);
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
		return left.expr().product(right.expr());
	}

	@Override
	public Multiplicities mergeMults(Multiplicities other) {
		if (other instanceof ArrowMult) {
			Multiplicity n = Multiplicity.mergeMult(this.mult, other.mult);
        	return new ArrowMult(this.left.mergeMults(((ArrowMult) other).left), this.right.mergeMults(((ArrowMult) other).right), n);
		}
		else if (other instanceof LeafMult && other.equals(Multiplicities.univ(this.arity))) 
			return this;
		else 
			return new MixedMult(this, other);
	}

}