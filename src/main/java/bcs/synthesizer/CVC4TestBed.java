package bcs.synthesizer;

import java.util.ArrayList;

import bcs.benchmark.Benchmark;

public class CVC4TestBed {

	/*
	 * private static String buildCVCQuery(String targetProgram, Benchmark
	 * benchmark, ArrayList<String> remainingPrograms) {
	 * 
	 * String targetFunctionString = benchmark.getFunString().replace("funToken;",
	 * targetProgram );
	 * 
	 * 
	 * 
	 * 
	 * String tmp = benchmark.getFunString(); tmp = tmp.substring(0,
	 * tmp.lastIndexOf(")")); tmp = tmp.substring(0, tmp.lastIndexOf(")")); tmp +=
	 * ") Bool)"; tmp = tmp.replace("define-fun", "synth-fun"); tmp =
	 * tmp.replace(benchmark.getFunctionName(), "pred");
	 * 
	 * String synthFunctionString = tmp;
	 * 
	 * String predicateFunctionInvocation = "(pred"; ArrayList<String>
	 * firstInvocation = benchmark.getInvocations().get(0); for (int i = 0; i <
	 * firstInvocation.size(); i++) { predicateFunctionInvocation += " " +
	 * firstInvocation.get(i); }
	 * 
	 * predicateFunctionInvocation += ")";
	 * 
	 * String targetFunctionInvocation = "(" + benchmark.getFunctionName(); for (int
	 * i = 0; i < firstInvocation.size(); i++) { targetFunctionInvocation += " " +
	 * firstInvocation.get(i); } targetFunctionInvocation += ")";
	 * 
	 * ArrayList<String> remainingProgramDefinitions = new ArrayList<String>();
	 * ArrayList<String> remainingProgramInvocations = new ArrayList<>(); if
	 * (remainingPrograms != null) { for (int i = 0; i < remainingPrograms.size();
	 * i++) {
	 * remainingProgramDefinitions.add(benchmark.getFunString().replace("funToken;",
	 * remainingPrograms.get(i)) .replace(benchmark.getFunctionName(),
	 * benchmark.getFunctionName() + "_" + i));
	 * remainingProgramInvocations.add(targetFunctionInvocation.replace("(" +
	 * benchmark.getFunctionName(), "(" + benchmark.getFunctionName() + "_" + i)); }
	 * }
	 * 
	 * 
	 * String query = "(set-logic " + benchmark.getLogic() + ")\n"; query +=
	 * targetFunctionString + "\n"; query += synthFunctionString + "\n";
	 * 
	 * if (benchmark.getDefinedFunctions() != null) { for (int i = 0; i <
	 * benchmark.getDefinedFunctions().length; i++) { query +=
	 * benchmark.getDefinedFunctions()[i] + "\n"; } }
	 * 
	 * for (int i = 0; i < remainingProgramDefinitions.size(); i++) { query +=
	 * remainingProgramDefinitions.get(i) + "\n"; }
	 * 
	 * 
	 * for (int i = 0; i < benchmark.getVariableNames().length; i++) { query +=
	 * "(declare-var " + benchmark.getVariableNames()[i] + " " +
	 * benchmark.getVariableTypes()[i] + ")\n"; }
	 * 
	 * String distinctnessString = "(and true";
	 * 
	 * for (int i = 0; i < remainingProgramInvocations.size(); i++) {
	 * distinctnessString += " (distinct " + targetFunctionInvocation + " " +
	 * remainingProgramInvocations.get(i) + ")";
	 * 
	 * }
	 * 
	 * 
	 * distinctnessString += ")"; String assertionString =
	 * benchmark.getAssertionString(); String parPattern = "(" +
	 * benchmark.getFunctionName(); String uniqueCorrectnessString = "true"; if
	 * (remainingPrograms != null) { if (remainingPrograms.size() == 1) {
	 * uniqueCorrectnessString = "(assert (not " +
	 * assertionString.replace(parPattern, parPattern + "_" + 0) + "))\n"; } else {
	 * uniqueCorrectnessString = "(not ( and  "; for (int i = 0; i <
	 * remainingPrograms.size(); i++) { uniqueCorrectnessString +=
	 * assertionString.replace(parPattern, parPattern + "_" + i) + "\n "; }
	 * uniqueCorrectnessString += "))\n"; } }
	 * 
	 * query += "(constraint (=> " + predicateFunctionInvocation+ " " +
	 * benchmark.getAssertionString() + "))\n"; query += "(constraint (=> (not " +
	 * predicateFunctionInvocation + ") " + "(not " + benchmark.getAssertionString()
	 * + ")))\n"; query += "(check-synth)";
	 * 
	 * for (int i = 0; i < benchmark.getFunctionVariables().length; i++) { query =
	 * query.replace("tmpvar" + (i+1) + ";", benchmark.getFunctionVariables()[i]); }
	 * 
	 * //targetFunctionString.substring(funString.indexOf(benchmark.getFunctionName(
	 * )) + benchmark.getFunctionName().length(), //
	 * funString.lastIndexOf("funToken;"))
	 * 
	 * //System.out.println(query); return query; }
	 */

	private static String buildCVCQuery(String targetProgram, Benchmark benchmark) {

		String targetFunctionString = benchmark.getFunString().replace("funToken;", targetProgram);

		String tmp = benchmark.getFunString();
		tmp = tmp.substring(0, tmp.lastIndexOf(")"));
		tmp = tmp.substring(0, tmp.lastIndexOf(")"));
		tmp += ") Bool)";
		tmp = tmp.replace("define-fun", "synth-fun");
		tmp = tmp.replace(benchmark.getFunctionName(), "pred");

		String synthFunctionString = tmp;

		String predicateFunctionInvocation = "(pred";
		ArrayList<String> firstInvocation = benchmark.getInvocations().get(0);
		for (int i = 0; i < firstInvocation.size(); i++) {
			predicateFunctionInvocation += " " + firstInvocation.get(i);
		}

		predicateFunctionInvocation += ")";

		String query = "(set-logic " + benchmark.getLogic() + ")\n";
		query += targetFunctionString + "\n";
		query += synthFunctionString + "\n";

		if (benchmark.getDefinedFunctions() != null) {
			for (int i = 0; i < benchmark.getDefinedFunctions().length; i++) {
				query += benchmark.getDefinedFunctions()[i] + "\n";
			}
		}

		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			query += "(declare-var " + benchmark.getVariableNames()[i] + " " + benchmark.getVariableTypes()[i] + ")\n";
		}

		query += "(constraint (=> " + predicateFunctionInvocation + " " + benchmark.getAssertionString() + "))\n";
		query += "(constraint (=> (not " + predicateFunctionInvocation + ") " + "(not " + benchmark.getAssertionString()
				+ ")))\n";
		query += "(check-synth)";

		for (int i = 0; i < benchmark.getFunctionVariables().length; i++) {
			query = query.replace("tmpvar" + (i + 1) + ";", benchmark.getFunctionVariables()[i]);
		}

		System.out.println(query);
		return query;
	}

	/*public static void main(String[] args) throws Exception {

		String benchmarkFile = "src/main/resources/benchmarks/fg_max20.sl";

		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);

		for (int i = 0; i < 20; i++) {

			Process process = new ProcessBuilder("C:\\Users\\twels\\Documents\\CVC4\\cvc4-1.7-win64-opt.exe", "-L",
					"sygus").start();
			try (Writer w = new OutputStreamWriter(process.getOutputStream(), "UTF-8")) {
				w.write(buildCVCQuery("tmpvar1;", benchmark));
			}

			InputStream is = process.getInputStream();
			InputStreamReader isr = new InputStreamReader(is);
			try (BufferedReader br = new BufferedReader(isr)) {
				// String line;
				String status = br.readLine();

				//System.out.println(status);
				String returnedFunction = "";
				if (status.equals("unsat")) {
					returnedFunction = br.readLine();
				}

				//System.out.println(returnedFunction
						.substring(returnedFunction.lastIndexOf("Bool") + 4, returnedFunction.length() - 1).trim());

			}

			process.destroy();

		}

	}*/
	
	public static void main(String[] args) throws Exception {
		//String benchmarkFile = "src/main/resources/thatOne/mi_explainer.sl";
		String benchmarkFile = "src/main/resources/benchmarks/distinctOne.sl";
		Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
		//String cvcLocation = "C:\\Users\\twels\\Documents\\CVC4\\cvc4-1.7-win64-opt.exe";
		//String cvcLocation = "C:\\Users\\twels\\Documents\\CVC4\\cvc4-1.8-win64-opt.exe";
		//String cvcLocation = "C:\\Users\\twels\\Documents\\CVC4\\cvc4-1.8-win64-opt.exe";
		//String cvcLocation = "C:\\Users\\twels\\Documents\\cvc5\\cvc5.exe";
		String cvcLocation = "C:\\Users\\twels\\Documents\\cvc5\\cvc5-2021-09-04-win64-opt.exe";
		Synthesizer synth = new CVCPredicateSynthesizer(benchmark,cvcLocation);
		
		SynthesisParameters sp = new SynthesisParameters();
		sp.setMaxThreads(1);
		sp.setBranchwiseMode("CVC");
		sp.setSkipToRepair(true);
		//sp.setTimeout(2);
	//	SynthesisResult result = SynthesisMethods.runPartialThenPredicateSynthesis(partialsSynthesizer, predicateSynthesizer,benchmark,sp);
		//SynthesisResult result = SynthesisMethods.runProgramExtractionThenPredicateSynthesis(synth, benchmark, sp);
		SynthesisResult result = bcs.main.SynthesisMethods.runMIProgramExtractionThenPredicateSynthesis(synth, benchmark, sp);
		//String[] correctPrograms = buildMIStrings();
		//SynthesisResult result = SynthesisMethods.runPredicateSynthesis(correctPrograms, predicateSynthesizer, benchmark, sp);
		
		System.out.println("Successful?: " + (result.isSuccessful() ? "Yes" : "No"));
		if (result.isSuccessful()) {
			System.out.println("Program found: " + result.getProgramFound());
			System.out.println(result.getProgramFound().length());
		}
		System.out.println("Time taken: " + result.getTimeTaken() + " seconds");
		
	}
}
