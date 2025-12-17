package org.alloytools.solvers.natv.hypermc;

import static kodkod.util.nodes.AnnotatedNode.annotateRoots;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.alloytools.solvers.natv.electrod.ElectrodPrinter;
import org.alloytools.solvers.natv.electrod.ElectrodReader;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.AbortedException;
import kodkod.engine.HyperSolver;
import kodkod.engine.InvalidSolverParamException;
import kodkod.engine.Solution;
import kodkod.engine.Statistics;
import kodkod.engine.TemporalSolver;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Reporter;
import kodkod.engine.fol2sat.FormulaFlattener;
import kodkod.engine.fol2sat.Skolemizer;
import kodkod.engine.ltl2fol.NNFReplacer;
import kodkod.engine.ltl2fol.TemporalBoundsExpander;
import kodkod.engine.satlab.ExternalSolver;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.engine.unbounded.InvalidUnboundedProblem;
import kodkod.engine.unbounded.InvalidUnboundedSolution;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleSet;
import kodkod.solvers.api.NativeCode;
import kodkod.solvers.api.TemporalSolverFactory;
import kodkod.util.nodes.AnnotatedNode;

abstract class HyperMCSolverRef extends SATFactory implements TemporalSolverFactory {

    private static final long serialVersionUID = 1L;
    final File                electrod;
    final File                solver;
    final String              solverId;

    class HyperMCSolver implements HyperSolver<ExtendedOptions> {

        final ExtendedOptions options;

        HyperMCSolver(ExtendedOptions options) {
            if (options == null)
                throw new NullPointerException();
            this.options = options;
            if (!options.unbounded() && options.minTraceLength() != 1)
                throw new InvalidSolverParamException("Electrod bounded model checking must start at length 1.");
            if (options.noOverflow())
                throw new InvalidSolverParamException("Electrod model checking does not support preventing integer overflows.");

        }

        /**
         * {@inheritDoc}
         */
        public ExtendedOptions options() {
            return options;
        }

        /**
         * {@inheritDoc}
         */
        public Solution solve(Formula formula, PardinusBounds bounds) throws InvalidUnboundedProblem, InvalidUnboundedSolution {
            if (!options.decomposed() && bounds.amalgamated != null)
                bounds = bounds.amalgamated();

            options.reporter().solvingCNF(-1, -1, -1, -1);

            // retrieve the additional formula imposed by the symbolic
            // bounds, depending on execution stage
            Formula symbForm = Formula.TRUE;
            // if decomposed mode, the amalgamated bounds are always considered
            if (options.decomposed() && bounds.amalgamated() != null)
                symbForm = bounds.amalgamated().resolve(options.reporter());
            // otherwise use regular bounds
            else
                symbForm = bounds.resolve(options.reporter());
            // NOTE: this is already being performed inside the translator, but is not accessible
            formula = formula.and(symbForm);
            formula = NNFReplacer.nnf(formula);
            AnnotatedNode<Formula> annotated = annotateRoots(formula);
            annotated = FormulaFlattener.flatten(annotated, true);

            formula = Skolemizer.skolemize(annotated, bounds, options).node();
            Map<Relation,String> rel2name = new HashMap<>();
            String electrod = ElectrodPrinter.print(formula, bounds, rel2name, options);

            return executeDry(this, electrod, bounds, rel2name);
        }

    }

    public HyperMCSolverRef(String solver) {
        solverId = solver;
        this.electrod = NativeCode.platform.getExecutable("electrod").orElse(null);
        this.solver = solverId == null ? null : NativeCode.platform.getExecutable(solver).orElse(null);
    }

    @Override
    public boolean isPresent() {
        return electrod != null && solver != null;
    }

    @Override
    public String[] getExecutables() {
        return new String[] {
                             "electrod", solverId
        };
    }

    @Override
    public boolean isTransformer() {
        return false;
    }

    @Override
    public String type() {
        return "exteral";
    }


    @Override
    public boolean incremental() {
        return false;
    }

    @Override
    public int trace() {
        return 2;
    }

    @Override
    public SATSolver instance() {
        if (solverId == null)
            return new ExternalSolver("electrod", null, true);
        else
            return new ExternalSolver("electrod", null, true, "-t", solverId);
    }

    @Override
    public TemporalSolver<ExtendedOptions> getTemporalSolver(ExtendedOptions options) {
        return new HyperMCSolver(options);
    }

    Solution executeDry(HyperMCSolver electrodSolver, String elo, PardinusBounds bounds, Map<Relation,String> rel2name) {
        boolean dry = electrodSolver.options.isLast() == null;

        Reporter reporter = electrodSolver.options.reporter();

        Process process = null;
        String output = null;
        Exception exception = null;
        int exitCode = Integer.MAX_VALUE;
        ProcessBuilder processBuilder = new ProcessBuilder();
        Map<String,String> environment = processBuilder.environment();
        if (solver != null)
            environment.put("PATH", addSolverToPath(environment.get("PATH"), solver));
        List<String> args = processBuilder.command();
        args.add(electrod.getAbsolutePath());
        args.add("--na");
        args.add("--kg");
        args.add("--ln");
        args.add("--only-used=false");
        if (!dry)
            args.add("--sf");
        if (electrodSolver.options.noMultBounds())
            args.add("--do-bounds=false");
        if (electrodSolver.options.tempSymmetries())
            args.add("--temporal-symmetry");


        if (ExtendedOptions.isDebug())
            args.add("-v");

        ExtendedOptions options = electrodSolver.options();
        if (!options.unbounded()) {
            args.add("--bmc");
            args.add(Integer.toString(options.maxTraceLength()));
        }

        try {
            File tempDir = Files.createTempDirectory(options.uniqueName()).toFile();
            File eloFile = new File(tempDir, "output.elo");
            write(eloFile, elo);
            File out = new File(tempDir, ".out");
            args.add(eloFile.getAbsolutePath());
            processBuilder.redirectError(out);
            processBuilder.redirectOutput(out);
            reporter.debug("starting electrod process with : " + args);

            process = processBuilder.start();
            exitCode = process.waitFor();
            output = read(out);

            if (exitCode == 0) {
                String smvName = tempDir.list((File dir, String name) -> name.endsWith(".smv"))[0];
                File smvFile = new File(tempDir, smvName);

                if (!dry) {

                    // define hp file from SMV LTLPEC
                    Pattern pattern = Pattern.compile("\\nLTLSPEC(.*?);", Pattern.DOTALL);
                    Matcher matcher = pattern.matcher(read(smvFile));
                    matcher.find();
                    String hpContent = matcher.group(1).trim();
                    pattern = Pattern.compile("([a-zA-Z0-9#_-]*)-_([a-zA-Z0-9#_-]*)####0([a-zA-Z0-9#_-]*)");
                    matcher = pattern.matcher(hpContent);
                    hpContent = matcher.replaceAll("$1$3[$2]");
                    hpContent = options.isLast().get(0) + "\n" + hpContent;


                    if (solver != null) {
                        File hpFile = new File(tempDir, "prop.hp");
                        Files.write(hpFile.toPath(), hpContent.getBytes());

                        // run hypersmv
                        File hs = NativeCode.platform.getExecutable("hypersmv").orElse(null);
                        args.clear();
                        args.add(hs.getAbsolutePath());
                        args.add("ah");
                        options.isLast().subList(4, options.isLast().size()).forEach(x -> args.add((String) x));

                        args.add("--informula=" + hpFile.getAbsolutePath());
                        args.add("--ahsolver=forq");
                        //                    args.add("--debug=True");
                        args.add("--witness=True");
                        args.add("--docker=hyperalloy/hypercheckers-arm64");

                        try (BufferedReader br = new BufferedReader(new FileReader("hypersmv.config"))) {
                            String firstLine = br.readLine();
                            args.addAll(Arrays.asList(firstLine.split(" ")));
                        } catch (Exception e) {
                        }


                        processBuilder = new ProcessBuilder(args);
                        process = processBuilder.start();
                        processBuilder.redirectErrorStream(true);
                        BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));

                        String line;
                        while ((line = reader.readLine()) != null) {
                            line = line;
                        }
                        exitCode = process.waitFor();

                        // run MC solver
                        args.clear();
                        File el = NativeCode.platform.getExecutable("electrod").orElse(null);
                        args.add(el.getAbsolutePath());
                        args.add("A.witness");
                        File f = new File((String) options.isLast().get(1), "output.info");
                        args.add("--bt");
                        args.add(f.getAbsolutePath());

                        processBuilder = new ProcessBuilder(args);
                        process = processBuilder.start();
                        processBuilder.redirectErrorStream(true);
                        reader = new BufferedReader(new InputStreamReader(process.getInputStream()));

                        while ((line = reader.readLine()) != null) {
                            line = line;
                        }
                        exitCode = process.waitFor();

                        File xmlFile = new File("A.xml");
                        String xmlLink = String.format("%05d.xml", bounds.integration);
                        File link = new File(tempDir, xmlLink);
                        Files.createLink(link.toPath(), xmlFile.toPath());

                        TupleSet atom = bounds.upperBound((Relation) options.isLast().get(2));

                        ElectrodReader rd = new ElectrodReader(bounds, rel2name, atom);
                        TemporalInstance temporalInstance = rd.read(read(xmlFile));

                        Bounds outerbds = (Bounds) options.isLast().get(3);

                        List<Instance> new_instances = new ArrayList<Instance>();
                        // project into outermost quantifier trace
                        for (int i = 0; i < temporalInstance.prefixLength(); i++) {
                            Instance instance = new Instance(outerbds.universe());
                            for (Relation r : outerbds.relations()) {
                                for (Relation r2 : temporalInstance.state(i).relations()) {
                                    if (r.name().equals(r2.name())) {
                                        TupleSet ts;

                                        if (r.arity() == r2.arity())
                                            ts = temporalInstance.state(i).tuples(r2);
                                        else {
                                            ts = bounds.universe().factory().noneOf(r.arity());
                                            temporalInstance.state(i).tuples(r2).forEach(t -> {
                                                List<Object> ats = new ArrayList();
                                                for (int k = 1; k < r2.arity(); k++)
                                                    ats.add(t.atom(k));
                                                ts.add(bounds.universe().factory().tuple(ats));
                                            });

                                        }

                                        instance.add(r, TemporalBoundsExpander.convertToUniv(ts, outerbds.universe()));
                                        break;
                                    }
                                }
                                if (!instance.contains(r))
                                    if (outerbds.lowerBound(r).size() == outerbds.upperBound(r).size())
                                        instance.add(r, outerbds.upperBound(r));
                                    else
                                        throw new RuntimeException("Unbound relation: " + r);

                            }
                            new_instances.add(instance);
                        }

                        temporalInstance = new TemporalInstance(new_instances, temporalInstance.loop, temporalInstance.unrolls);

                        Statistics stats = new Statistics(rd.nbvars, 0, 0, rd.ctime, rd.atime);
                        Solution solution = temporalInstance == null ? Solution.unsatisfiable(stats, null) : Solution.satisfiable(stats, temporalInstance);
                        return solution;
                    } else {
                        File hpFile = new File("prop.hp");
                        Files.write(hpFile.toPath(), hpContent.getBytes());

                        String xmlLink = String.format("%05d.xml", bounds.integration);
                        File link = new File(tempDir, xmlLink);
                        Files.createLink(link.toPath(), hpFile.toPath());

                        Solution solution = Solution.unsatisfiable(null, null);
                        solution.setOutput(hpFile);
                        return solution;

                    }
                } else {
                    String xmlLink = String.format("%05d.xml", bounds.integration);
                    File link = new File(tempDir, xmlLink);
                    Files.createLink(link.toPath(), smvFile.toPath());

                    Solution solution = Solution.unsatisfiable(null, null);
                    solution.setOutput(smvFile);
                    return solution;
                }

            }

        } catch (

        InterruptedException e) {
            Thread.currentThread().interrupt();
            exception = e;
        } catch (Exception e) {
            exception = e;
        } finally {
            if (process != null)
                process.destroy();
        }
        String report = "electrod exit code: " + exitCode + ":\n  args=" + args.stream().collect(Collectors.joining(" ")) + "\n  output=" + output;
        reporter.debug(report);
        throw new AbortedException(report);
    }

    private String addSolverToPath(String PATH, File solverPath) {
        String dir = solverPath.getParent();
        if (PATH == null) {
            return dir;
        } else
            return dir + File.pathSeparator + PATH;
    }

    private String read(File file) throws Exception {
        try {
            if (file != null && file.isFile()) {
                byte[] allBytes = Files.readAllBytes(file.toPath());
                return new String(allBytes, StandardCharsets.UTF_8);
            }
        } catch (Exception e) {
            return e.toString();
        }
        return "no file " + file;
    }

    private void write(File file, String contents) throws Exception {
        Files.write(file.toPath(), contents.getBytes(StandardCharsets.UTF_8));
    }

    @Override
    public String id() {
        return "electrod.hypermcsf";
    }

    @Override
    public Optional<String> getDescription() {
        return Optional.ofNullable("a BMC for hyper-properties, generates SMV files for models and an HQ file with a hyper formula; models as a single LTLSPEC formula");
    }

    @Override
    public String check() {
        return "todo: need to check electrod/HyperMC combination in some way";
    }
}
