package bcs.branchwisePredicateSynthesis.helpers;

import java.util.concurrent.Callable;

import bcs.benchmark.Benchmark;
import bcs.branchwisePredicateSynthesis.BranchwisePredicateSynthesis;
import bcs.synthesizer.Synthesizer;
import bcs.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class BPSCallable implements Callable<BPSJobResult> {

	private BranchwisePredicateSynthesis job;
	private Synthesizer synthesizer;
	private String globalConstraintsString = "";
	private Benchmark benchmark;
	private double pctOfPositives;
	private boolean verifySuccess;
	private int completeMappingsFound;
	private String branchwiseMode;

	public BPSCallable(BranchwisePredicateSynthesis job, Synthesizer synthesizer,
			Benchmark benchmark, String globalConstraintsString, double pctOfPositives, boolean verifySuccess, int completeMappingsFound, String branchwiseMode) {
		this.job = job;
		this.synthesizer = synthesizer;
		this.globalConstraintsString = globalConstraintsString;
		this.benchmark = benchmark;
		this.pctOfPositives = pctOfPositives;
		this.verifySuccess = verifySuccess;
		this.completeMappingsFound = completeMappingsFound;
		this.branchwiseMode = branchwiseMode;
	}

	@Override
	public BPSJobResult call() throws Exception {

		Verifier verifier = new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
				null);

		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setPctOfPositives(pctOfPositives);
		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
		
		if (!globalConstraintsString.isEmpty()) {
			verifier.setGlobalConstraints(globalConstraintsString.split(",,,"));
		} 
		verifier.setSynthType("predicate");
		
		job.run(verifier, synthesizer,verifySuccess,completeMappingsFound, branchwiseMode);
		return new BPSJobResult(job);
	}

}
