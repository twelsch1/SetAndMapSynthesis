package testbed;

import evoSynthesis.GPPartialsSynthesizer;
import evoSynthesis.GPPredicateSynthesizer;
import sms.benchmark.Benchmark;
import sms.main.SynthesisMethods;
import sms.synthesizer.SynthesisParameters;
import sms.synthesizer.SynthesisResult;
import sms.synthesizer.Synthesizer;

public class SingleRunTestBed {

	public static void main(String[] args) throws Exception {

		//String benchmarkFile = "src/main/resources/benchmarks/fg_array_search_10.sl";
		//String benchmarkFile = "src/main/resources/benchmarks/darkOne.sl";
		String benchmarkFile = "src/main/resources/benchmarks/fg_array_search_4.sl";
		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
		
		String[] synthesisVariableNames = new String[benchmark.getVariableNames().length];
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			synthesisVariableNames[i] = "var" + (i+1) + ";";
		}
		
		benchmark.setSynthesisVariableNames(synthesisVariableNames);
		
		String paramFile = "src/main/resources/booleanchild.params";
		String scgpFile = "src/main/resources/defineFunIntChild.params";
	
		GPPartialsSynthesizer gpPartialsSynthesizer = new GPPartialsSynthesizer(scgpFile,benchmark);
		Synthesizer partialsSynthesizer = gpPartialsSynthesizer;
	

		Synthesizer predicateSynthesizer = new GPPredicateSynthesizer(paramFile,benchmark);
		SynthesisParameters sp = new SynthesisParameters();
		sp.setMaxThreads(1);
		//sp.setSkipToRepair(true);
		//sp.setTimeout(2);
		//SynthesisResult result = SynthesisMethods.CEGIS(partialsSynthesizer, benchmark);
	SynthesisResult result = SynthesisMethods.runPartialThenPredicateSynthesis(partialsSynthesizer, predicateSynthesizer,benchmark,sp);
	//	SynthesisResult result = SynthesisMethods.runMIProgramExtractionThenPredicateSynthesis(predicateSynthesizer, benchmark, sp);
		//SynthesisResult result = SynthesisMethods.runProgramExtractionThenPredicateSynthesis(partialsSynthesizer, predicateSynthesizer, benchmark, sp);
		//System.out.println("Successful?: " + (result.isSuccessful() ? "Yes" : "No"));
		if (result.isSuccessful()) {
			//System.out.println("Program found: " + result.getProgramFound());
			//System.out.println(result.getProgramFound().length());
		}
		//System.out.println("Time taken: " + result.getTimeTaken() + " seconds");
		
	}
}
