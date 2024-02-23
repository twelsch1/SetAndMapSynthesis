package sms.deterministicSMS;

import java.io.BufferedWriter;
import java.io.FileWriter;

import sms.benchmark.Benchmark;
import sms.main.SynthesisMethods;
import sms.synthesizer.CVCPredicateSynthesizer;
import sms.synthesizer.SynthesisParameters;
import sms.synthesizer.SynthesisResult;
import sms.synthesizer.Synthesizer;

public class DeterministicSMS {

	
	public static void main(String[] args) throws Exception {
		if (args.length < 1) {
			//System.out.println("No benchmark file provided");
			System.exit(0);
		}
		
		if (args.length < 2) {
			//System.out.println("No CVC location provided");
			System.exit(0);
		}
		String benchmarkFile = args[0];
		String cvcLocation = args[1];
		
		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
		
		//String cvcLocation = "src/main/resources/cvc5-2021-09-04-win64-opt.exe";
		//String cvcLocation = "C:\\Users\\twels\\Documents\\cvc5\\cvc5-2021-09-04-win64-opt.exe";
		Synthesizer synth = new CVCPredicateSynthesizer(benchmark,cvcLocation);
		
		SynthesisParameters sp = new SynthesisParameters();
		sp.setMaxThreads(1);
		sp.setBranchwiseMode("CVC");
		sp.setSkipToRepair(true);
		//sp.setTimeout(2);
	//	SynthesisResult result = SynthesisMethods.runPartialThenPredicateSynthesis(partialsSynthesizer, predicateSynthesizer,benchmark,sp);
		//SynthesisResult result = SynthesisMethods.runProgramExtractionThenPredicateSynthesis(synth, benchmark, sp);
		SynthesisResult result = sms.main.SynthesisMethods.deterministicSMS(synth, benchmark, sp, cvcLocation);
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
