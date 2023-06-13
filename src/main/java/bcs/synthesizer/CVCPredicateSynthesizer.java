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

	private String buildCVCQuery(String targetProgram, Benchmark benchmark, String[] remainingPartials, String[] globalConstraints) {

		
		
		
		
		String targetFunctionString = benchmark.getFunString().replace("funToken;", targetProgram);
		System.out.println(targetFunctionString);

		String funcName = benchmark.getFunctionName();
		String parPattern = "(" + funcName;
		
		String funString = benchmark.getFunString();
		String assertionString = benchmark.getAssertionString();
		String tmp = benchmark.getFunString();
		System.out.println("FUN STRING " + tmp);
		tmp = tmp.substring(0, tmp.lastIndexOf(")"));
		tmp = tmp.substring(0, tmp.lastIndexOf(")"));
		tmp += ") Bool)";
		tmp = tmp.replace("define-fun", "synth-fun");
		tmp = tmp.replace("synth-fun " + funcName,  "synth-fun pred");
		System.out.println(tmp);

		
		String remPartialsDefinitions = "";
		String remPartialsAssertions = "";
		
		
		if (remainingPartials != null && remainingPartials.length != 0) {
			
			remPartialsAssertions = "(or false";
			for (int i = 0; i < remainingPartials.length; i++) {
				remPartialsDefinitions += funString.replace("(define-fun " + benchmark.getFunctionName(), 
						"(define-fun " + funcName + "_remaining_" + i).replace("funToken;",
						remainingPartials[i]) + "\n";
				
				remPartialsAssertions += assertionString.replace(parPattern, parPattern + "_remaining_" + i) + "\n";
			}
			
			remPartialsAssertions += ")";
			
			

			
		}
		
		String gcs = "true";
		
		if (globalConstraints != null && globalConstraints.length != 0) {
			gcs = "(and true";
			for (int i = 0; i < globalConstraints.length; i++) {
				gcs += " (not " + globalConstraints[i] + ")\n";
			}
			
			gcs += ")";
		}
		
		
		//System.out.println(remPartialsDefinitions);
		//System.out.print(remPartialsAssertions);
		
		
		
		
		
		String synthFunctionString = tmp;

		String predicateFunctionInvocation = "(pred";
		String[] principalInvocation = benchmark.getVariableNames();
		for (int i = 0; i < principalInvocation.length; i++) {
			predicateFunctionInvocation += " " + principalInvocation[i];
		}

		predicateFunctionInvocation += ")";
		
		

		String query = "(set-logic " + benchmark.getLogic() + ")\n";
		if (benchmark.getDefinedFunctions() != null) {
			for (int i = 0; i < benchmark.getDefinedFunctions().length; i++) {
				query += benchmark.getDefinedFunctions()[i] + "\n";
			}
		}

		query += targetFunctionString + "\n";
		query += synthFunctionString + "\n";
		//query += remPartialsDefinitions;
		

		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			query += "(declare-var " + benchmark.getVariableNames()[i] + " " + benchmark.getVariableTypes()[i] + ")\n";
		}

				
		query += "(constraint (=> " + predicateFunctionInvocation + " " + benchmark.getAssertionString() + "))\n";
		
				
		query += "(constraint (=> (not " + predicateFunctionInvocation + ") " + "(not " + benchmark.getAssertionString()
			+ ")))\n";
		
		
	/*	query += "(constraint (=> " + gcs + " ";
		query +="(and ";
		
		query += "(=> " + predicateFunctionInvocation + " " + benchmark.getAssertionString() + ") \n";
		
		query += "(=> (not " + predicateFunctionInvocation + ") " + "(or (not " + benchmark.getAssertionString() + ") " + remPartialsAssertions;
		query += "))\n";
				
		query+= ")";		
		
		
		query += "))";
		*/
		
		
		query += "(check-synth)";

		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			
			query = query.replace("var" + (i + 1) + ";", benchmark.getVariableNames()[i]);
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
			
			
			
			//process = new ProcessBuilder(cvcLocation, "-L", "sygus", "--sygus-si", "all", "sygus-out"
				//	.start();
			
			process = new ProcessBuilder(cvcLocation, "-L", "sygus2", "--sygus-si", "all", "--sygus-out", "status-and-def")
					.start();


			//System.out.println(buildCVCQuery(verifier.getTargetPartial(), benchmark));
			//System.out.println("Partial " + verifier.getTargetPartial());
			String query = buildCVCQuery(verifier.getTargetPartial(), benchmark, verifier.getRemainingPartials(), verifier.getGlobalConstraints());
			

			System.out.println(query);
			try (Writer w = new OutputStreamWriter(process.getOutputStream(), "UTF-8")) {
				System.out.println("FIRE!");
				w.write(query);
				
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
				throw e;
			} catch (IOException e) {
				e.printStackTrace();
				throw e;
			}

			InputStream is = process.getInputStream();
			InputStreamReader isr = new InputStreamReader(is);
			//isr.
			
			try (BufferedReader br = new BufferedReader(isr)) {
				String line;
				line = br.readLine();
				System.out.println(line);
				String cvcResponse = "";
				while ((line = br.readLine()) != null) {
				    cvcResponse += line;
				}
				
				System.out.println(cvcResponse);
				
				if (!cvcResponse.isEmpty()) {

				program = cvcResponse.substring(cvcResponse.lastIndexOf("Bool") + 4, cvcResponse.length() - 2).trim();
				success = true;
				
				}
				/*
				System.out.println(cvcResponse);
				String status = cvcResponse;
				System.out.println("Did we get anything? " + status);
				System.out.println(status);
				String returnedFunction = "";
				if (status.equals("unsat")) {
					
					returnedFunction = br.readLine();
					System.out.println("Returned function is " + returnedFunction);
					success = true;
					program = returnedFunction.substring(returnedFunction.lastIndexOf("Bool") + 4, returnedFunction.length() - 1).trim();
					
					System.out.println("Returned program was " + program);
				}*/



			}

		} catch (IOException e1) {
			e1.printStackTrace();
		} finally {
			process.destroy();
		}

		return new SynthesisResult(success, program);
	}
}
