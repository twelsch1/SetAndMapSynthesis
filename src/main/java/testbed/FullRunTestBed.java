package testbed;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;

import bcs.benchmark.Benchmark;
import bcs.main.SynthesisMethods;
import bcs.synthesizer.SynthesisParameters;
import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
import evoSynthesis.GPPartialsSynthesizer;
import evoSynthesis.GPPredicateSynthesizer;

public class FullRunTestBed {

	public static void main(String[] args) throws Exception {
		String directory = "src/main/resources/checkBenchmarks/";



		ArrayList<String> benchmarkNames = new ArrayList<>();
		File[] files = new File(directory).listFiles();
		for (File file : files) {
			benchmarkNames.add(file.getPath());
		}

		int numTrials = 1;
		int start = 1;

		String paramFile = "src/main/resources/booleanchildsilent.params";
		String scgpFile = "src/main/resources/defineFunIntChild.params";

		int sz = benchmarkNames.size();

		// int sz = 5;

		for (int i = start; i <= numTrials; i++) {
			String results = "Benchmark,Successful,Time Taken,Program Found,Program Length\n";

			//System.out.println("Number of benchmarks to synthesize: " + sz);
			for (int j = 0; j < sz; j++) {

				String benchmarkName = benchmarkNames.get(j);

				//System.out.println(benchmarkName);
				Benchmark benchmark = Benchmark.parseBenchmark(benchmarkName);
				
				String[] synthesisVariableNames = new String[benchmark.getVariableNames().length];
				for (int k = 0; k < benchmark.getVariableNames().length; k++) {
					synthesisVariableNames[k] = "var" + (k+1) + ";";
				}
				
				benchmark.setSynthesisVariableNames(synthesisVariableNames);
				
				GPPartialsSynthesizer gpPartialsSynthesizer = new GPPartialsSynthesizer(scgpFile, benchmark);
				Synthesizer partialsSynthesizer = gpPartialsSynthesizer;

				Synthesizer predicateSynthesizer = new GPPredicateSynthesizer(paramFile, benchmark);
				SynthesisParameters sp = new SynthesisParameters();
				sp.setMaxThreads(1);
				//sp.setBranchwiseMode("CBPS");
				
				SynthesisResult result = SynthesisMethods.runProgramExtractionThenPredicateSynthesis(
						partialsSynthesizer, predicateSynthesizer, benchmark, sp);

				results += benchmarkName + "," + result.asResultString() + "\n";
				//System.out.println("Successful?: " + (result.isSuccessful() ? "Yes" : "No"));
				if (result.isSuccessful()) {
					//System.out.println("Program found: " + result.getProgramFound());
					//System.out.println("Program Length: " + result.getProgramFound().length());
				}
				//System.out.println("Time taken: " + result.getTimeTaken() + " seconds");

				BufferedWriter writer = new BufferedWriter(new FileWriter("results" + i + ".csv"));
				writer.write(results);

				writer.close();

			}

		}

	}

}
