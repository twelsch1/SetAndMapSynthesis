package bcs.jobs;

import java.util.ArrayList;
import java.util.concurrent.Callable;

import com.microsoft.z3.Status;

import bcs.benchmark.Benchmark;
import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
import bcs.verification.VerificationResult;
import bcs.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SCCallable implements Callable<SCJobResult>  {

	private SplitAndCoverProgramSynthesis parentJob;

	private ArrayList<String> correctTerms;
	private ArrayList<String> additionalTerms;
	private Synthesizer partialsSynthesizer;
	private Benchmark benchmark;
	private boolean verifySuccess;
	
	public SCCallable(Synthesizer partialsSynthesizer, Benchmark benchmark, SplitAndCoverProgramSynthesis parentJob,
			ArrayList<String> correctTerms, ArrayList<String> additionalTerms, boolean verifySuccess) {
		this.partialsSynthesizer = partialsSynthesizer;
		this.benchmark = benchmark;
		this.parentJob = parentJob;
		this.correctTerms = correctTerms;
		this.additionalTerms = additionalTerms;
		this.verifySuccess = verifySuccess;
	}

	@Override
	public SCJobResult call() throws Exception {
		
		Verifier verifier =  new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), parentJob.getExtraAssertions(), benchmark.getFunString(), 
				benchmark.getAssertionString(),
				"LIA", 
				correctTerms.toArray(new String[correctTerms.size()]));
		
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setAdditionalTerms(additionalTerms.toArray(new String[additionalTerms.size()]));
		verifier.setSynthType("program");
		
		SynthesisResult sr = parentJob.run(verifier, partialsSynthesizer);
		
		SplitAndCoverProgramSynthesis[] childJobs = null;
		
		if (!sr.isSuccessful() && !sr.getSplit().isEmpty()) {
				childJobs = parentJob.split(sr.getSplit());
		}
		

		if (sr.isSuccessful() && verifySuccess) {
			VerificationResult vr = verifier.verify(sr.getProgramFound());
			if (vr.getStatus() != Status.UNSATISFIABLE) {
				throw new Exception("Synthesizer returned successful SynthesisResult when programFound is incorrect");
			}
			
		}
		
		return new SCJobResult(sr.isSuccessful(),parentJob,childJobs, sr.getProgramFound());
	}

	public SplitAndCoverProgramSynthesis getParentJob() {
		return parentJob;
	}
	
	
	
}
