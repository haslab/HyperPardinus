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
package kodkod.test.pardinus.temporal;

import static org.junit.Assert.assertFalse;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.Universe;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.Timeout;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

/**
 * A set of LTL identities that must hold for all backends (within reasonable
 * trace lengths for bounded ones).
 * 
 * @author Nuno Macedo // [HASLab] temporal model finding
 *
 */
@RunWith(Parameterized.class)
public class TemporalIdentitiesTests {
	private PardinusSolver dsolver;
	private ExtendedOptions opt;
	static private Relation g = Relation.unary_variable("g"), h = Relation.unary_variable("h"), i  = Relation.unary_variable("i");
	static private Formula p = g.some(), q = h.some(), r = i.some(), tt = g.eq(g), ff = g.eq(g).not();
	
	@Rule
    public Timeout globalTimeout = Timeout.seconds(60);

	private Formula v1;
	private SATFactory v2;
	private boolean v3;
	
	public TemporalIdentitiesTests(Formula v1, SATFactory v2, boolean v3) {
		this.v1 = v1;
		this.v2 = v2;
		this.v3 = v3;
	}

	@Parameters(name = "{0} {1} {2}")
	public static Collection<Object[]> data() {
		Object[][] data = new Object[][] {
			{(p.after().always()).iff(p.always().after()), 																	SATFactory.DEFAULT,					false}, // t81
			{(p.always()).iff(p.not().eventually().not()), 																	SATFactory.DEFAULT,					false}, // t83
			{(ff.after()).iff(ff), 																							SATFactory.DEFAULT,					false}, // t85
			{(ff.eventually()).iff(ff), 																					SATFactory.DEFAULT,					false}, // t87
			{((p.after().until(q)).and(r)).iff(((p.after()).until(q)).and(r)),												SATFactory.DEFAULT,					false}, // t89
			{(tt.after()).iff(tt), 																							SATFactory.DEFAULT,					false}, // t91
			{(ff.always()).iff(ff), 																						SATFactory.DEFAULT,					false}, // t92
			{(tt.eventually()).iff(tt), 																					SATFactory.DEFAULT,					false}, // t94
			{(ff.eventually().eventually()).iff(ff.eventually()),															SATFactory.DEFAULT,					false}, // t95
			{(tt.always()).iff(tt), 																						SATFactory.DEFAULT,					false}, // t97
			{(ff.always().always()).iff(ff.always()), 																		SATFactory.DEFAULT,					false}, // t98
			{(p.until(tt)).iff(tt), 																						SATFactory.DEFAULT,					false}, // t100
			{(ff.until(p)).iff(p), 																							SATFactory.DEFAULT,					false}, // t101
			{(p.until(ff)).iff(ff), 																						SATFactory.DEFAULT,					false}, // t102
			{(p.until(p)).iff(p), 																							SATFactory.DEFAULT,					false}, // t103
			{(tt.until(p)).iff(p.eventually()), 																			SATFactory.DEFAULT,					false}, // t104
			{((p.after()).until(q.after())).iff((p.until(q)).after()), 														SATFactory.DEFAULT,					false}, // t105
			{(p.releases(q)).iff(((p.not()).until(q.not())).not()), 														SATFactory.DEFAULT,					false}, // t107
			{(p.releases(tt)).iff(tt), 																						SATFactory.DEFAULT,					false}, // t108
			{(p.releases(ff)).iff(ff), 																						SATFactory.DEFAULT,					false}, // t109
			{(tt.releases(p).iff(p)), 																						SATFactory.DEFAULT,					false}, // t110
			{(p.releases(p).iff(p)), 																						SATFactory.DEFAULT,					false}, // t111
			{(ff.releases(p).iff(p.always())), 																				SATFactory.DEFAULT,					false}, // t112
			{(p.releases(q)).iff(q.and(p.or((p.releases(q)).after()))), 													SATFactory.DEFAULT,					false}, // t113
			{(p.always().eventually().after()).iff(p.always().eventually()), 												SATFactory.DEFAULT,					false}, // t115
			{(p.eventually().always().after()).iff(p.eventually().always()), 												SATFactory.DEFAULT,					false}, // t116
			{(p.eventually().after()).iff(p.after().eventually()), 															SATFactory.DEFAULT,					false}, // t117
			{((p.until(q)).eventually()).iff(q.eventually()), 																SATFactory.DEFAULT,					false}, // t119
			{((p.and(q.after())).always().eventually()).iff((p.and(q)).always().eventually()), 								SATFactory.DEFAULT,					false}, // t120
			{((p.and(q.always())).always().eventually()).iff((p.and(q)).always().eventually()), 							SATFactory.DEFAULT,					false}, // t121
			{((p.or(q.always())).always().eventually()).iff((p.always().or(q.always())).eventually()), 						SATFactory.DEFAULT,					false}, // t122
			{((p.and(q.eventually())).always().eventually()).iff((p.always().eventually()).and(q.eventually().always())),	SATFactory.DEFAULT,					false}, // t123
			{((p.or(q.eventually())).always().eventually()).iff((p.always().eventually()).or(q.eventually().always())),		SATFactory.DEFAULT,					false}, // t124
			{((p.or(q.after())).eventually().always()).iff((p.or(q)).eventually().always()),								SATFactory.DEFAULT,					false}, // t126
			{((p.or(q.eventually())).eventually().always()).iff((p.or(q)).eventually().always()),							SATFactory.DEFAULT,					false}, // t127
			{((p.and(q.eventually())).eventually().always()).iff(((p.eventually()).and(q.eventually())).always()),			SATFactory.DEFAULT,					false}, // t128
			{((p.and(q.always())).eventually().always()).iff((p.eventually().always()).and(q.always().eventually())),		SATFactory.DEFAULT,					false}, // t129
			{((p.or(q.always())).eventually().always()).iff((p.eventually().always()).or(q.always().eventually())),			SATFactory.DEFAULT,					false}, // t130
			{(p.until(p.always())).iff(p.always()),																			SATFactory.DEFAULT,					false}, // t132
			{(p.releases(p.eventually())).iff(p.eventually()),																SATFactory.DEFAULT,					false}, // t133	
			{((p.always().eventually()).and(q.always().eventually())).iff((p.and(q)).always().eventually()),				SATFactory.DEFAULT,					false}, // t136
			{((p.after()).and(q.after())).iff((p.and(q)).after()),															SATFactory.DEFAULT,					false}, // t137
			{((p.after()).and(q.always().eventually())).iff((p.and(q.always().eventually())).after()),						SATFactory.DEFAULT,					false}, // t138
			{((p.until(q)).and(r.until(q))).iff((p.and(r)).until(q)),														SATFactory.DEFAULT,					false}, // t139
			{((p.releases(q)).and(p.releases(r))).iff(p.releases(q.and(r))),												SATFactory.DEFAULT,					false}, // t140
			{((p.until(q)).or(p.until(r))).iff(p.until(q.or(r))),															SATFactory.DEFAULT,					false}, // t141
			{((p.releases(q)).or(r.releases(q))).iff((p.or(r)).releases(q)),												SATFactory.DEFAULT,					false}, // t142
			{((q.always()).or(p.releases(q))).iff(p.releases(q)),															SATFactory.DEFAULT,					false}, // t144
			{((p.after()).releases(q.after())).iff((p.releases(q)).after()),												SATFactory.DEFAULT,					false}, // t147
			{((p.releases(q)).always()).iff(q.always()),																	SATFactory.DEFAULT,					false}, // t149
			{(p.once().always().eventually()).iff(p.eventually()),															SATFactory.DEFAULT,					false}, // t151
			{((p.and(q.since(r))).eventually()).iff((r.and(p.or((q.until(q.and(p))).after()))).eventually()),				SATFactory.DEFAULT,					false}, // t153
		};
		return Arrays.asList(data);
	}
	
	@Test
	public void test() {
		int n = 3;
		
		final List<String> atoms = new ArrayList<String>(n);

		for (int i = 0; i <= n; i++)
			atoms.add("n" + i);

		Universe u = new Universe(atoms);
		final TupleFactory f = u.factory();
		final PardinusBounds b = new PardinusBounds(u);
		
		b.bound(g, f.range(f.tuple("n0"), f.tuple("n"+n)));
		b.bound(h, f.range(f.tuple("n0"), f.tuple("n"+n)));
		b.bound(i, f.range(f.tuple("n0"), f.tuple("n"+n)));
		
		opt = new ExtendedOptions();
		opt.setRunTemporal(true);
		opt.setRunDecomposed(false);
		opt.setMaxTraceLength(10);
		opt.setSolver(v2);
		opt.setRunUnbounded(v3);
		dsolver = new PardinusSolver(opt);
		Solution sol = dsolver.solve(v1.not(), b);
		
		assertFalse(sol.sat());

	}

}
