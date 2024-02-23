package sms.learningSMS;

import java.io.BufferedWriter;
import java.io.FileWriter;

import evoSynthesis.GPPartialsSynthesizer;
import evoSynthesis.GPPredicateSynthesizer;
import sms.benchmark.Benchmark;
import sms.main.SynthesisMethods;
import sms.synthesizer.CVCPredicateSynthesizer;
import sms.synthesizer.SynthesisParameters;
import sms.synthesizer.SynthesisResult;
import sms.synthesizer.Synthesizer;

public class LearningSMS {

	
	public static void main(String[] args) throws Exception {
		if (args.length < 1) {
			//System.out.println("No benchmark file provided");
			System.exit(0);
		}
		

		String scSynthFile = "src/main/resources/defineFunIntChild.params";
		String predSynthFile = "src/main/resources/booleanchildsilent.params";
	
		
		if (args.length > 1) {
			scSynthFile = args[1];
			predSynthFile = args[2];
		}
		String benchmarkFile = args[0];

		
		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
	
		GPPartialsSynthesizer gpPartialsSynthesizer = new GPPartialsSynthesizer(scSynthFile,benchmark);
		Synthesizer partialsSynthesizer = gpPartialsSynthesizer;
	

		Synthesizer predicateSynthesizer = new GPPredicateSynthesizer(predSynthFile,benchmark);
		SynthesisParameters sp = new SynthesisParameters();
		sp.setMaxThreads(1);
		//sp.setSkipToRepair(true);
		//sp.setTimeout(2);
		//SynthesisResult result = SynthesisMethods.CEGIS(partialsSynthesizer, benchmark);
		SynthesisResult result = SynthesisMethods.runPartialThenPredicateSynthesis(partialsSynthesizer, predicateSynthesizer,benchmark,sp);
		//String[] correctPrograms = buildMIStrings();
		//SynthesisResult result = SynthesisMethods.runPredicateSynthesis(correctPrograms, predicateSynthesizer, benchmark, sp);
		String results = "Benchmark,Successful,Time Taken,Program Found,Program Length\n";
		results += benchmarkFile + "," + result.asResultString() + "\n";
		System.out.println("Successful?: " + (result.isSuccessful() ? "Yes" : "No"));
		if (result.isSuccessful()) {
			System.out.println("Program found: " + result.getProgramFound());
			System.out.println("Program Length: " + result.getProgramFound().length());
		}
		System.out.println("Time taken: " + result.getTimeTaken() + " seconds");

		BufferedWriter writer = new BufferedWriter(new FileWriter("DeterministicSMSresult.csv"));
		writer.write(results);

		writer.close();
	}
}
