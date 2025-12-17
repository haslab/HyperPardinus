package kodkod.ast;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import kodkod.ast.operator.Multiplicity;

public abstract class Multiplicities {
	
    private static final Map<Integer, Multiplicities> empties = new HashMap<Integer,Multiplicities>();
    private static final Map<Integer, Multiplicities> univs = new HashMap<Integer,Multiplicities>();

    private static Multiplicities power(int a, Expression e) {
    	Multiplicities m = new LeafMult(e, Multiplicity.SET);
    	Multiplicities p = m;
    	for (int i = 1; i < a; i ++)
    		p = new ArrowMult(p,m,Multiplicity.SET);
    	return p;
    }
    
    public static Multiplicities empty(int arity) {
        return empties.computeIfAbsent(arity, a -> power(a,Expression.NONE) );
    }
    
    public static Multiplicities univ(int arity) {
        return univs.computeIfAbsent(arity, a -> power(a,Expression.UNIV) );
    }
    
	final public Multiplicity mult;
	final public int arity;
	public final boolean exact;

	public Multiplicities(int arity, Multiplicity mult, boolean exact) {
		if (exact && !mult.equals(Multiplicity.SET))
			throw new IllegalArgumentException("Exact must be set.");
		this.mult = mult;
		this.arity = arity;
		this.exact = exact;
	}
	protected abstract List<Expression> domains();
	public abstract void replace(Expression e1, Expression e2);

	public abstract Multiplicities mergeMults(Multiplicities other);

	public abstract Expression expr();

	
}