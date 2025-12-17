package kodkod.ast;

import java.util.ArrayList;
import java.util.List;

import kodkod.ast.operator.Multiplicity;

public class LeafMult extends Multiplicities {
	private Expression expr;
	
	public LeafMult(Expression expr, Multiplicity mult) {
		this(expr, mult, false);
	}

	public LeafMult(Expression expr, Multiplicity mult, boolean exact) {
		super(expr.arity(), mult, exact);
		this.expr = expr;
	}

	@Override
	protected List<Expression> domains() {
		List<Expression> l = new ArrayList<Expression>();
		l.add(expr);
		return l;
	}

	@Override
	public void replace(Expression e1, Expression e2) {
		if (expr.equals(e1))
			expr = e2;
	}

	@Override
	public Expression expr() {
		return expr;
	}

	@Override
	public Multiplicities mergeMults(Multiplicities other) {
		if (other instanceof ArrowMult && this.equals(Multiplicities.univ(this.arity)))
			return other.mergeMults(this);
		
		else if (other instanceof LeafMult) {
			
			if (this.equals(Multiplicities.univ(this.arity)))
				return other;
			
			Expression e1 = this.expr(), e2 = ((LeafMult) other).expr;
	        
			if (e1.toString().equals(e2.toString())) {
	        	Multiplicity n = Multiplicity.mergeMult(this.mult,other.mult);
	        	return new LeafMult(e1, n);
	        }
	        else if (this.mult.equals(other.mult))
	        	return new LeafMult(e1.intersection(e2), this.mult);
	        else 
	        	return new MixedMult(this,other);
        }
		else 
			return new MixedMult(this,other);
	}
	
}