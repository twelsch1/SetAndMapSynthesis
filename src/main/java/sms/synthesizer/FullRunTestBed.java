package sms.synthesizer;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;

import sms.benchmark.Benchmark;
import sms.main.SynthesisMethods;

public class FullRunTestBed {

	public static void main(String[] args) throws Exception {
		String directory = "src/main/resources/DetSMSBenchmarks/";
		//String directory = "src/main/resources/benchmarks/";


		ArrayList<String> benchmarkNames = new ArrayList<>();
		File[] files = new File(directory).listFiles();
		for (File file : files) {
			benchmarkNames.add(file.getPath());
		}
		
		String cvcLocation = "C:\\Users\\twels\\Documents\\cvc5\\cvc5-2021-09-04-win64-opt.exe";

		int numTrials = 1;
		int start = 1;

		int sz = benchmarkNames.size();

		// int sz = 5;

		for (int i = start; i <= numTrials; i++) {
			String results = "Benchmark,Successful,Time Taken,Program Length\n";

			////System.out.println("Number of benchmarks to synthesize: " + sz);
			for (int j = 0; j < sz; j++) {

				String benchmarkName = benchmarkNames.get(j);

				//System.out.println(benchmarkName);
				Benchmark benchmark = Benchmark.parseBenchmark(benchmarkName);
				CVCPredicateSynthesizer predSynth = new CVCPredicateSynthesizer(benchmark, cvcLocation);
				CVCSolver synth = new CVCSolver(benchmark, cvcLocation);
				SynthesisParameters sp = new SynthesisParameters();
				sp.setMaxThreads(1);
				sp.setSkipToRepair(true);
				sp.setBranchwiseMode("CVC");
				// sp.set
				SynthesisResult result = SynthesisMethods.deterministicSMS(predSynth, benchmark, sp, cvcLocation);
				//SynthesisResult result = new SynthesisResult(false, 3600);
				//SynthesisResult result = SynthesisMethods.CVC5Direct(synth, benchmark);
				//SynthesisResult result = new SynthesisResult(false,"",3600);
				results += benchmarkName + "," + result.asResultString() + "\n";
				
				//System.out.println("Successful?: " + (result.isSuccessful() ? "Yes" : "No"));
				if (result.isSuccessful()) {
					//System.out.println("Program found: " + result.getProgramFound());
					//System.out.println("Program Length: " + result.getProgramFound().length());
				} else {
					System.out.println("RED ALERT!");
					System.out.println(benchmarkName);
				}
				//System.out.println("Time taken: " + result.getTimeTaken() + " seconds");

				BufferedWriter writer = new BufferedWriter(new FileWriter("multipleinvocation" + ".csv"));
				writer.write(results);

				writer.close();

			}

		}

	}

}
