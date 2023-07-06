package bcs.multipleInvocation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;

import bcs.benchmark.Benchmark;
import bcs.main.SynthesisMethods;
import bcs.verification.Verifier;

public class MIUtils {

	
	public static ArrayList<String> determineUnfixedVariables(ArrayList<ArrayList<String>> invocations) {
		ArrayList<String> unfixedVariables = new ArrayList<>();
		HashSet<String> uvSet = new HashSet<>();
		ArrayList<String> primeInvocation = invocations.get(0);
		for (int i = 1; i < invocations.size(); i++) {
			ArrayList<String> inv = invocations.get(i);
			for (int j = 0; j < inv.size(); j++) {
				if (!inv.get(j).equals(primeInvocation.get(j))) {
					uvSet.add(inv.get(j));
					uvSet.add(primeInvocation.get(j));
				}
				
			}
		}
		
		
		unfixedVariables.addAll(uvSet);
		Collections.sort(unfixedVariables);
		//Collections.reverse(unfixedVariables);
		
		return unfixedVariables;
	}
	
	public static boolean containsUnfixedVariables(String predicate, ArrayList<String> unfixedVariables, ArrayList<String> variables) {
		
		for (String s : unfixedVariables) {
			if (predicate.contains(transformProgramFromInvocationToTempVars(s, variables))) {
				return true;
			}
		}
		
		return false;
	}
	public static String transformProgramFromInvocationToTempVars(String program, ArrayList<String> templateInvocation) {
		String tmpSynthString = program;
		if (!program.contains("(")) {
			for (int i = 0; i < templateInvocation.size(); i++) {
				if (tmpSynthString.contains(templateInvocation.get(i))) {
					tmpSynthString = tmpSynthString.replace(templateInvocation.get(i), "var" + (i+1) + ";");
					return tmpSynthString;
				}
				
			}

		} else {
			for (int i = 0; i < templateInvocation.size(); i++) {
				//System.out.println(tmpSynthString);
				tmpSynthString = tmpSynthString.replace(" " + templateInvocation.get(i) + " ", " var" + (i+1) + "; ");
				tmpSynthString = tmpSynthString.replace(templateInvocation.get(i) + ")", "var" + (i+1) + ";)");
				tmpSynthString = tmpSynthString.replace("(" + templateInvocation.get(i) + " ", "(var" + (i+1) + "; ");
				
				//System.out.println("um " + templateInvocation.get(i));
			}
		}
		
		return tmpSynthString;
	}
	
	public static String transformProgramFromInvocations(String program, ArrayList<String> templateInvocation, ArrayList<String> targetInvocation) {
		String tmpSynthString = transformProgramFromInvocationToTempVars(program, templateInvocation);		
		return transformProgramFromTempVarsToInvocation(tmpSynthString, targetInvocation);
	}
	
	public static String transformProgramFromTempVarsToInvocation(String program, ArrayList<String> targetInvocation) {
		String retVal = program;
		
		for (int i = 0; i < targetInvocation.size(); i++) {
			retVal = retVal.replace("var" + (i+1) + ";", targetInvocation.get(i));
		}
		
		return retVal;
		
	}
	
	public static String constructInterchangeableProgram(String program, ArrayList<ArrayList<String>> eqInvocations,
			ArrayList<String> principalInvocation, String predicate
			) {
		

		
		ArrayList<String> predicates = new ArrayList<> ();
		predicates.add(predicate);
		for (int i = 0; i < eqInvocations.size()-1; i++) {
			String pred = MIUtils.transformProgramFromTempVarsToInvocation(predicate, principalInvocation);
			String synthPred = MIUtils.transformProgramFromInvocationToTempVars(pred, eqInvocations.get(i));
			predicates.add(synthPred);
		}

		
		ArrayList<String> programs = new ArrayList<>();
		programs.add(program);
		
		for (int i = 0; i < eqInvocations.size(); i++) {
			String prog =  MIUtils.transformProgramFromTempVarsToInvocation(program, principalInvocation);
			String synthProg = MIUtils.transformProgramFromInvocationToTempVars(prog, eqInvocations.get(i));
			programs.add(synthProg);
		}

		
		String retVal = "";
		String closingParens = "";
		for (int i = 0; i < predicates.size(); i++) {
			retVal += "(ite " + predicates.get(i) + " " + programs.get(i) + " ";
			closingParens += ")";
		}
		
		
		retVal += programs.get(programs.size()-1) + closingParens;
		
	
		
		return retVal;
	}
	
	public static InvocationsConfiguration buildMIConfiguration(String program, ArrayList<ArrayList<String>> invocations,
			ArrayList<String> partials, Verifier verifier) throws Exception {

		ArrayList<ArrayList<String>> eqInvocations = new ArrayList<>();
		ArrayList<ArrayList<String>> distInvocations = new ArrayList<>();
		for (int i = 0; i < invocations.size(); i++) {
			distInvocations.add(invocations.get(i));
			verifier.setDistInvocations(distInvocations);
			verifier.setEqInvocations(eqInvocations);
			if (!verifier.verifyInterchangeableConfiguration(program, partials.toArray(new String[partials.size()]))) {
				//System.out.println("Removing from dist and adding to equality on program " + program);
				distInvocations.remove(distInvocations.size() - 1);
				eqInvocations.add(invocations.get(i));
			}

		}

		return new InvocationsConfiguration(eqInvocations, distInvocations);
	}
	
	public static ArrayList<String> extractPossibleInterchangeablePrograms(String program, ArrayList<ArrayList<String>> nonPrincipalInvocations,
			ArrayList<String> partials, Verifier verifier, ArrayList<String> principalInvocation) throws Exception {
		//////System.out.println("Hey");
		ArrayList<String> possiblePrograms = new ArrayList<>();
		ArrayList<InvocationsConfiguration> previousConfigurations = new ArrayList<>();
		previousConfigurations.add(new InvocationsConfiguration(new ArrayList<ArrayList<String>>(), nonPrincipalInvocations));
		verifier.setPreviousConfigurations(previousConfigurations);
		
		while (verifier.verifyProgramCanSatisfy(program, partials.toArray(new String[partials.size()]))) {
			InvocationsConfiguration nextConfiguration = MIUtils.buildMIConfiguration(program, nonPrincipalInvocations,
					partials, verifier);

			String predicate = MIUtils.generateMIPredicate(nextConfiguration.getEqInvocations(), principalInvocation);
			////System.out.println("Predicate " + predicate);

			possiblePrograms.add(MIUtils.constructInterchangeableProgram(program, nextConfiguration.getEqInvocations(),
					principalInvocation, predicate));
			System.out.println("Constructed " + possiblePrograms.get(possiblePrograms.size()-1));

			previousConfigurations.add(nextConfiguration);
			

		}
		
		
		
		
		return possiblePrograms;
	}
	
	public static String generateMIPredicate(ArrayList<ArrayList<String>> relevantInvocations, ArrayList<String> principalInvocation) {
		String retVal = "";
		String closingParen = "";
		
		
		
        ArrayList<ArrayList<String>> relevantPlusPrincipalInvocations = new ArrayList<>();
        relevantPlusPrincipalInvocations.addAll(relevantInvocations);
        relevantPlusPrincipalInvocations.add(principalInvocation);
		ArrayList<String> unfixedVariables = MIUtils.determineUnfixedVariables(relevantPlusPrincipalInvocations);
		//for (String s : unfixedVariables) {
			////System.out.println(s);
		//}
		ArrayList<String> synthVarUnfixedVariables = new ArrayList<>();
		
		for (int i = 0; i < unfixedVariables.size(); i++) {
			////System.out.println(	MIUtils.transformProgramFromInvocationToTempVars(unfixedVariables.get(i), principalInvocation));

			synthVarUnfixedVariables.add(MIUtils.transformProgramFromInvocationToTempVars(unfixedVariables.get(i), principalInvocation));
		}
		if (unfixedVariables.size() > 2) {
			retVal = "(and";
			closingParen = ")";
		}
		
		for (int i = 0; i < synthVarUnfixedVariables.size()-1; i++) {
			retVal += " (>= " + synthVarUnfixedVariables.get(i) + " " + synthVarUnfixedVariables.get(i+1) + ")";
			//retVal += " (> " + synthVarUnfixedVariables.get(i) + " " + synthVarUnfixedVariables.get(i+1) + ")";
		}
		
		retVal += closingParen;
		
		
		
		return retVal.trim();
		
		
	}
	
	private static ArrayList<String> interchangeableProgramExtraction(ArrayList<String> programsExtractedSoFar, Verifier verifier,
			ArrayList<ArrayList<String>> nonPrincipalInvocations, ArrayList<String> principalInvocation) throws Exception {
	
		ArrayList<String> partials = new ArrayList<>();
		partials.addAll(programsExtractedSoFar);
		for (String s: programsExtractedSoFar) {
			
			//////System.out.println(s);
			partials.addAll(MIUtils.extractPossibleInterchangeablePrograms(s, nonPrincipalInvocations, partials, verifier, principalInvocation));
			

		}
		
		return partials;
		
	}
	
	private static void distinctProgramExtraction(ArrayList<InvocationsConfiguration> configurations,
			ArrayList<String> partials,
			ArrayList<String> principalInvocation, Verifier verifier
			) throws Exception {
		

		
		while (!configurations.isEmpty()) {
			InvocationsConfiguration ic = configurations.remove(0);
			while (verifier.verifyDistinctConfigurationCanSatisfy(ic.getMainProgram(), ic.getEqInvocations(), ic.getDistInvocations(), partials, configurations)) {
				String partial = MIUtils.extractPossibleDistinctProgramFromConfig(ic, partials, configurations, principalInvocation, verifier);
				partials.add(partial);
				
			}
		}

		
	}
	
	private static void distinctConfigurationExtraction(ArrayList<String> programsExtractedSoFar, 
			ArrayList<InvocationsConfiguration> configurations, Verifier verifier, 
			ArrayList<ArrayList<String>> nonPrincipalInvocations, ArrayList<String> principalInvocation) throws Exception {
		for (String s : programsExtractedSoFar) {
			//Note this adds to configurations
			MIUtils.extractPossibleDistinctConfiguration(s, programsExtractedSoFar, configurations, nonPrincipalInvocations, principalInvocation, verifier);
		}
		
		
	}
	
	public static void extractPossibleDistinctConfiguration(String program, ArrayList<String> partials,
			ArrayList<InvocationsConfiguration> configurations, ArrayList<ArrayList<String>> nonPrincipalInvocations,
			ArrayList<String> principalInvocation, Verifier verifier) throws Exception {

		if (verifier.verifyProgramCanSatisfyDistinct(program, partials, configurations)) {
			// build a configuration and add it to configurations
			ArrayList<ArrayList<String>> eqInvocations = new ArrayList<>();
			ArrayList<ArrayList<String>> distInvocations = new ArrayList<>();

			for (ArrayList<String> inv : nonPrincipalInvocations) {
				eqInvocations.add(inv);
				
				if (!verifier.verifyDistinctConfigurationCanSatisfy(program, eqInvocations, distInvocations, partials, configurations)) {
					eqInvocations.remove(eqInvocations.size()-1);
					//eqInvocations.remov
					distInvocations.add(inv);
				}
			}
			
			//System.out.println(program);
			configurations.add(new InvocationsConfiguration(program, eqInvocations, distInvocations));

		}
	}
	
	
	public static String[] automaticSatisfyingSetConstruction(Benchmark benchmark) throws Exception {
		
		Verifier verifier = new Verifier(benchmark.getFunctionName(), 
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), 
				benchmark.getLogic(), null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
	
		

		
		String[] variables = benchmark.getVariableNames();
		ArrayList<String> variablesList = new ArrayList<>();
		for (int i = 0; i < variables.length; i++) {
			variablesList.add(variables[i]);
		}
		
		ArrayList<ArrayList<String>> nonPrincipalInvocations = new ArrayList<>();
		ArrayList<ArrayList<String>> invocations = new ArrayList<>();
		invocations.addAll(benchmark.getInvocations());	
		invocations.remove(variablesList);
		nonPrincipalInvocations.addAll(invocations);
		invocations.add(0, variablesList);
				
		String[] extracts = SynthesisMethods.directProgramExtractionRedux(benchmark);
		
		ArrayList<String> extracted = new ArrayList<>();
		ArrayList<String> possiblePrograms = new ArrayList<String>();
		for (int i = 0; i < extracts.length; i++) {
			extracted.add(extracts[i]);
			possiblePrograms.add(extracts[i]);
		}
		

		
		
		if (verifier.verifyMIPartials(extracted, possiblePrograms, null)) {
			return verifier.MIReduceToNecessarySet(extracted, possiblePrograms);
		}
		
		extracted = MIUtils.interchangeableProgramExtraction(extracted, verifier, nonPrincipalInvocations, variablesList);
		

		if (verifier.verifyMIPartials(extracted, possiblePrograms, null)) {
			
		  return  verifier.MIReduceToNecessarySet(extracted, possiblePrograms);
/*
		 
		  String[] retVal = new String[pre.length];
		  
		  
		 
		  int j = 0;
		  for (int i = pre.length-1; i >= 0; i--) {
			  System.out.println("Included " + MIUtils.transformProgramFromTempVarsToInvocation(pre[i], variablesList));
			  //retVal[j] = pre[i];
			  retVal[i] = pre[i];
			  j++;
		  }
		 
		//  return pre;
		  return retVal;*/

			
		}
		

		ArrayList<InvocationsConfiguration> configurations = new ArrayList<>();
		do {
			System.out.println("Looping");
			MIUtils.distinctConfigurationExtraction(extracted, configurations, verifier, nonPrincipalInvocations,
					variablesList);
		} while (!verifier.verifyMIPartials(extracted, possiblePrograms,configurations));
		

		verifier.MIReduceToNecessaryConfigurations(extracted, possiblePrograms, configurations);
		//System.out.println("mocks constructed");
		MIUtils.distinctProgramExtraction(configurations, extracted, variablesList, verifier);
		
		  return verifier.MIReduceToNecessarySet(extracted, possiblePrograms);
		  
		  /*
		  String[] retVal = new String[pre.length];
		  
		  int j = 0;
		  for (int i = pre.length-1; i >= 0; i--) {
			  //System.out.println("Included " + pre[i]);
			  retVal[j] = pre[i];
			  j++;
		  }*/
		  
		  //return retVal;
		//return verifier.MIReduceToNecessarySet(extracted);
	}
	
	private static void theFinalCountdown() throws Exception {
		Benchmark benchmark = Benchmark.parseBenchmark("src/main/resources/benchmarks/darkOne.sl");
		
		Verifier verifier = new Verifier(benchmark.getFunctionName(), 
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), 
				benchmark.getLogic(), null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());

		String[] extracted = MIUtils.automaticSatisfyingSetConstruction(benchmark);
		for (int i = 0; i < extracted.length; i++) {
			//System.out.println(extracted[i]);
		}

	}

	public static String constructDistinctProgram(String program, ArrayList<String> distinctPrograms, ArrayList<ArrayList<String>> eqInvocations,
			ArrayList<String> principalInvocation
			) {
		
		String predicate = MIUtils.generateMIPredicate(eqInvocations, principalInvocation);
		
		ArrayList<String> predicates = new ArrayList<> ();
		predicates.add(predicate);
		for (int i = 0; i < eqInvocations.size()-1; i++) {
			String pred = MIUtils.transformProgramFromTempVarsToInvocation(predicate, principalInvocation);
			String synthPred = MIUtils.transformProgramFromInvocationToTempVars(pred, eqInvocations.get(i));
			predicates.add(synthPred);
		}

		
		ArrayList<String> programs = new ArrayList<>();
		programs.add(program);
		programs.addAll(distinctPrograms);
		
		String retVal = "";
		String closingParens = "";
		for (int i = 0; i < predicates.size(); i++) {
			retVal += "(ite " + predicates.get(i) + " " + programs.get(i) + " ";
			closingParens += ")";
		}
		
		
		retVal += programs.get(programs.size()-1) + closingParens;
		
		return retVal;
	} 
	
	public static ArrayList<String> calculateEligibleProgramsActual(ArrayList<String> programsFoundSoFar, ArrayList<String> possibleEligiblePrograms, 
			ArrayList<String> partials, ArrayList<InvocationsConfiguration> configurations, Verifier verifier) throws Exception {
		ArrayList<String> eligiblePrograms = new ArrayList<>();
 		for (int i = 0; i < possibleEligiblePrograms.size(); i++) {
			String programToCheck = possibleEligiblePrograms.get(i);
			if (programsFoundSoFar.contains(programToCheck)) {
				continue;
			}
			//////System.out.println("Program to check: " + programToCheck);
			if (verifier.verifyProgramEligibleActual(programToCheck, programsFoundSoFar, partials, configurations)) {
				eligiblePrograms.add(programToCheck);
				//////System.out.println("eligible");
			} else {
				//////System.out.println("Ineligible");
			}
			
			
		}
		
		
		
		
		return eligiblePrograms;
	}
	
	public static ArrayList<String> calculateDistinctPrograms(ArrayList<String> distinctProgramsSoFar, ArrayList<String> possiblePrograms, 
			ArrayList<String> unfixedVariables, Verifier verifier) throws Exception {
		ArrayList<String> eligiblePrograms = new ArrayList<>();
 		for (int i = 0; i < possiblePrograms.size(); i++) {
			String programToCheck = possiblePrograms.get(i);

			//////System.out.println("Program to check: " + programToCheck);
			if (verifier.verifyIsAlwaysDistinct(distinctProgramsSoFar, programToCheck, unfixedVariables)) {
				eligiblePrograms.add(programToCheck);
				//////System.out.println("eligible");
			}
			
			
		}
		
		
		
		
		return eligiblePrograms;
	}
	
	public static String extractPossibleDistinctProgramFromConfig(InvocationsConfiguration configToCheck, 
			ArrayList<String> partials, ArrayList<InvocationsConfiguration> configurations, ArrayList<String> principalInvocation,
			Verifier verifier) throws Exception {
		ArrayList<ArrayList<String>> eqInvocations = new ArrayList<>();
		eqInvocations.addAll(configToCheck.getEqInvocations());
		ArrayList<ArrayList<String>> distInvocations = new ArrayList<>();
		distInvocations.addAll(configToCheck.getDistInvocations());
		
		InvocationsConfiguration ic = new InvocationsConfiguration(configToCheck.getMainProgram(), 
				eqInvocations, distInvocations);
		ArrayList<String> programsFoundSoFar = new ArrayList<>();
		programsFoundSoFar.add(configToCheck.getMainProgram());
		ArrayList<String> eligiblePrograms = new ArrayList<String>();
		eligiblePrograms.addAll(partials);
		
		ArrayList<ArrayList<String>> invocationsForUnfixedVariables = new ArrayList<>();
		invocationsForUnfixedVariables.add(principalInvocation);
		invocationsForUnfixedVariables.addAll(configToCheck.getDistInvocations());

		
		ArrayList<String> unfixedVariables = MIUtils.determineUnfixedVariables(invocationsForUnfixedVariables);
		while (!ic.isDistInvocationsEmpty()) {
			
			
			
			eligiblePrograms = MIUtils.calculateDistinctPrograms(programsFoundSoFar, eligiblePrograms, unfixedVariables, verifier);
			eligiblePrograms = MIUtils.calculateEligibleProgramsActual(programsFoundSoFar, eligiblePrograms, partials, configurations, verifier);
			ArrayList<String> currentInvocation = ic.removeFirstDistinctInvocation();
			ic.addReplacementInvocation(currentInvocation);
			for (int i = 0; i < eligiblePrograms.size(); i++) {
				
				////System.out.println("Adding, pre size is " + ic.getReplacementPrograms().size() );
				ic.addReplacementProgram(eligiblePrograms.get(i));
				////System.out.println("Post size is " + ic.getReplacementPrograms().size() );

				if (verifier.verifyProgramCanReplaceActual(ic, partials, configurations)) {
					programsFoundSoFar.add(eligiblePrograms.get(i));
					////System.out.println("Success");
					break;
				} 
				
				ic.removeLastReplacementProgram();
			}
			
			
		}
		//Right now we calculate the predicate, build the program, and return it
		return MIUtils.constructDistinctProgramActual(ic, principalInvocation);
	}
	
	public static String constructDistinctProgramActual(InvocationsConfiguration ic,
			ArrayList<String> principalInvocation
			) {
		

		ArrayList<ArrayList<String>> replacementInvocations = ic.getReplacementInvocations();
		String predicate = MIUtils.generateMIPredicate(replacementInvocations, principalInvocation);
		
		
		ArrayList<String> predicates = new ArrayList<> ();
		predicates.add(predicate);
		
		for (int i = 0; i < replacementInvocations.size()-1; i++) {
			String pred = MIUtils.transformProgramFromTempVarsToInvocation(predicate, replacementInvocations.get(i));
			predicates.add(pred);
		}

		
		ArrayList<String> programs = new ArrayList<>();
		programs.add(ic.getMainProgram());
		programs.addAll(ic.getReplacementPrograms());
		
		//////System.out.println("Start");
		//for (String s : programs) {
			//////System.out.println(s);
		//}
		////System.out.println("End");
		
		String retVal = "";
		String closingParens = "";
		for (int i = 0; i < predicates.size(); i++) {
			retVal += "(ite " + predicates.get(i) + " " + programs.get(i) + " ";
			closingParens += ")";
		}
		
		
		retVal += programs.get(programs.size()-1) + closingParens;
		
		return retVal;
	}
	
	
	public static void extractPossibleDistinctProgramsActual(InvocationsConfiguration configToCheck,
			ArrayList<String> partials, ArrayList<InvocationsConfiguration> configurations,
			ArrayList<ArrayList<String>> nonPrincipalInvocations, ArrayList<String> principalInvocation,
			Verifier verifier) throws Exception {
		
		while(verifier.verifyDistinctConfigurationCanSatisfy(configToCheck.getMainProgram(),
				configToCheck.getDistInvocations(), configToCheck.getEqInvocations(), partials, configurations)) {
			
		}
		
	}
	
	
	public static void main(String[] args) throws Exception {
		theFinalCountdown();
	//	rockAndRoll();
		//hoochieCoo();
		/*
		String satProgram = "(- var1; var2;)";
		String unsatProgram = "( + (- var1; var2;) 1)";
		String altSatProgram = "(- var2; var1;)";
		String correctProgram = "(ite (>= var1; var2;) (- var1; var2;) (- var2; var1;))";
		
		String[] partials = new String[2];
		
		
		Benchmark benchmark = Benchmark.parseBenchmark("src/main/resources/benchmarks/diff.sl");
		Verifier verifier = new Verifier(benchmark.getFunctionName(), 
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), 
				benchmark.getLogic(), null);
		
		////System.out.println(verifier.verifyProgramCanSatisfy(satProgram, null));
		////System.out.println(verifier.verifyProgramCanSatisfy(unsatProgram, null));
		partials[0] = satProgram;
		partials[1] = altSatProgram;
		////System.out.println(verifier.verifyProgramCanSatisfy(satProgram, partials));
		partials[1] = correctProgram;
		////System.out.println(verifier.verifyProgramCanSatisfy(satProgram, partials));
		*/
		
		/*String predicate = "(>= var1; var2;)";
		
		ArrayList<String> variables = new ArrayList<>();
		variables.add("x");
		variables.add("y");
		
		ArrayList<String> secondInvocation = new ArrayList<>();
		secondInvocation.add("y");
		secondInvocation.add("x");
		
		ArrayList<ArrayList<String>> invocations = new ArrayList<>();
		invocations.add(variables);
		invocations.add(secondInvocation);
		
		ArrayList<String> programs = new ArrayList<>();
		programs.add("var1;");
		programs.add("var2;");
		
		////System.out.println(MIUtils.constructMIProgram(predicate, variables, invocations, programs));
		*/
		
		
		
		
		/*
		String program = "(ite (>= x y) x y)";
		String synthProgram = "(ite (>= var1; var2;) var1; var2;)";
		ArrayList<String> template = new ArrayList<>();
		template.add("x");
		template.add("y");
		
		ArrayList<String> target = new ArrayList<>();
		target.add("y");
		target.add("x");
		
		////System.out.println(MIUtils.transformProgramFromInvocations(program, template, target));
		////System.out.println(MIUtils.transformProgramFromTempVarsToInvocation(synthProgram, target));
		
		program = "x";
		synthProgram = "var1;";
		
		
		////System.out.println(MIUtils.transformProgramFromInvocations(program, template, target));
		////System.out.println(MIUtils.transformProgramFromTempVarsToInvocation(synthProgram, target));
		////System.out.println(MIUtils.transformProgramFromTempVarsToInvocation(synthProgram, template));
		*/
		
	}
}
