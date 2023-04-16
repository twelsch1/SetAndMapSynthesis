package bcs.synthesizer;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;
import java.util.ArrayList;

import bcs.benchmark.Benchmark;
import bcs.verification.Verifier;

public class CVCPredicateSynthesizer extends Synthesizer {

	private String cvcLocation;
	private Benchmark benchmark;

	public CVCPredicateSynthesizer(Benchmark benchmark, String cvcLocation) {
		this.benchmark = benchmark;
		this.cvcLocation = cvcLocation;
	}

	private String buildCVCQuery(String targetProgram, Benchmark benchmark) {

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
			query = query.replace("var" + (i + 1) + ";", benchmark.getFunctionVariables()[i]);
		}

		//System.out.println(query);
		return query;
	}

	//"C:\\Users\\twels\\Documents\\CVC4\\cvc4-1.7-win64-opt.exe"
	public SynthesisResult synthesize(Verifier verifier) {
		// SynthesisResult result = new SynthesisResult()
		String program = "";
		boolean success = false;

		Process process = null;
		try {
			process = new ProcessBuilder(cvcLocation, "-L", "sygus")
					.start();

			System.out.println("Partial " + verifier.getTargetPartial());
			try (Writer w = new OutputStreamWriter(process.getOutputStream(), "UTF-8")) {
				w.write(buildCVCQuery(verifier.getTargetPartial(), benchmark));
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
				throw e;
			} catch (IOException e) {
				e.printStackTrace();
				throw e;
			}

			InputStream is = process.getInputStream();
			InputStreamReader isr = new InputStreamReader(is);
			try (BufferedReader br = new BufferedReader(isr)) {
				String status = br.readLine();

				//System.out.println(status);
				String returnedFunction = "";
				if (status.equals("unsat")) {
					returnedFunction = br.readLine();
					success = true;
					program = returnedFunction.substring(returnedFunction.lastIndexOf("Bool") + 4, returnedFunction.length() - 1).trim();
				}



			}

		} catch (IOException e1) {
			e1.printStackTrace();
		} finally {
			process.destroy();
		}

		return new SynthesisResult(success, program);
	}
}
