package sms.main;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.HashSet;

import com.microsoft.z3.Status;

import sms.benchmark.Benchmark;
import sms.multipleInvocation.MIUtils;
import sms.programNode.Node;
import sms.synthesizer.CVCPredicateSynthesizer;
import sms.synthesizer.Preprocessor;
import sms.synthesizer.SynthesisParameters;
import sms.synthesizer.SynthesisResult;
import sms.synthesizer.Synthesizer;
import sms.utils.InterchangeableUtils;
import sms.utils.Utils;
import sms.verification.VerificationResult;
import sms.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SynthesisMethods {

	public static SynthesisResult runSTUNGP(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark) throws Exception {
		SynthesisParameters sp = new SynthesisParameters();
		sp.setEmulateSTUN(true);
		return runSTUNGP(partialsSynthesizer,predicateSynthesizer,benchmark,sp);
	}
	
	public static SynthesisResult runSTUNGP(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark, SynthesisParameters sp) throws Exception {
		sp.setEmulateSTUN(true);
		return runPartialThenPredicateSynthesis(partialsSynthesizer,predicateSynthesizer,benchmark,sp);
	}
	
	public static SynthesisResult CEGIS(Synthesizer synthesizer, Benchmark benchmark) throws Exception {
		SynthesisParameters sp = new SynthesisParameters();
		return CEGIS(synthesizer,benchmark,sp);
	}
		
	public static SynthesisResult CEGIS(Synthesizer synthesizer, Benchmark benchmark, SynthesisParameters sp) throws Exception {
		sp.setEmulateCEGIS(true);
		Instant start = Instant.now();
		String[] correctPrograms = SplitAndCover.SCGPDiscovery(synthesizer, benchmark, sp);
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		} else {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			return new SynthesisResult(true,correctPrograms[0],timeElapsed.toSeconds());
		}
	}
	
	public static SynthesisResult CVC5Direct(Synthesizer synthesizer, Benchmark benchmark) {
		Verifier verifier = new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
				null);
		
		Instant start = Instant.now();
		SynthesisResult sr = synthesizer.synthesize(verifier);

		Instant end = Instant.now();

		Duration timeElapsed = Duration.between(start, end);
		
		if (sr.isSuccessful()) {
		
		return new SynthesisResult(true, sr.getProgramFound(), timeElapsed.toSeconds());
		} else {
			return new SynthesisResult(false, "",3600);
		}
		
	}
	public static SynthesisResult runPartialThenPredicateSynthesis(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark) throws Exception {	
		SynthesisParameters sp = new SynthesisParameters();
		return runPartialThenPredicateSynthesis(partialsSynthesizer,predicateSynthesizer,benchmark,sp);
	}
	
	public static SynthesisResult runPartialThenPredicateSynthesis(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark, 
			SynthesisParameters sp) throws Exception {	
		
		Instant start = Instant.now();

		String[] correctPrograms = SplitAndCover.SCGPDiscovery(partialsSynthesizer, benchmark, sp);
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		}
		
		if (correctPrograms.length == 1) {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			return new SynthesisResult(true,correctPrograms[0],timeElapsed.toSeconds());
		}
		
		return SMS.constructMappingsAndUnify(predicateSynthesizer, benchmark, correctPrograms, start, sp);
		
	
		
		
	}
	
	public static SynthesisResult runProgramExtractionThenPredicateSynthesis(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark, 
			SynthesisParameters sp) throws Exception {	
		

		
		Instant start = Instant.now();
		
		String[] correctPrograms = null;
		String[] userSynthesisVariableNames = benchmark.getSynthesisVariableNames();
		
		String[] extractionVariableNames = new String[benchmark.getVariableNames().length];
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			extractionVariableNames[i] = "var" + (i+1) + ";";
		}
		
		benchmark.setSynthesisVariableNames(extractionVariableNames);
		correctPrograms = directProgramExtraction(benchmark);
		benchmark.setSynthesisVariableNames(userSynthesisVariableNames);
		/*if (correctPrograms == null) {
			//////System.out.println("Hello");
			correctPrograms = SplitAndConquer.SCGPDiscovery(partialsSynthesizer, benchmark, sp);
		}*/
		
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		}
		
		
		if (correctPrograms.length == 1) {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			
			String finalProgram = correctPrograms[0];
			for (int i = 0; i < benchmark.getVariableNames().length; i++) {
				finalProgram = finalProgram.replace(extractionVariableNames[i], benchmark.getVariableNames()[i]);
			}
			return new SynthesisResult(true,finalProgram,timeElapsed.toSeconds());
		}
		
		return SMS.constructMappingsAndUnify(predicateSynthesizer, benchmark, correctPrograms, start, sp);
		
	
		
		
	}
	
	public static SynthesisResult runProgramExtractionThenPredicateSynthesis(Synthesizer predicateSynthesizer, Benchmark benchmark, 
			SynthesisParameters sp) throws Exception {	
		

		
		Instant start = Instant.now();
		
		String[] correctPrograms = null;
		String[] userSynthesisVariableNames = benchmark.getSynthesisVariableNames();
		
		String[] extractionVariableNames = new String[benchmark.getVariableNames().length];
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			extractionVariableNames[i] = "var" + (i+1) + ";";
		}
		
		benchmark.setSynthesisVariableNames(extractionVariableNames);
		correctPrograms = directProgramExtraction(benchmark);
		benchmark.setSynthesisVariableNames(userSynthesisVariableNames);
		
		for (int i = 0; i < correctPrograms.length; i++) {
			////System.out.println(correctPrograms[i]);
		}
		/*if (correctPrograms == null) {
			//////System.out.println("Hello");
			correctPrograms = SplitAndConquer.SCGPDiscovery(partialsSynthesizer, benchmark, sp);
		}*/
		
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		}
		
		
		if (correctPrograms.length == 1) {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			
			String finalProgram = correctPrograms[0];
			for (int i = 0; i < benchmark.getVariableNames().length; i++) {
				finalProgram = finalProgram.replace(extractionVariableNames[i], benchmark.getVariableNames()[i]);
			}
			return new SynthesisResult(true,finalProgram,timeElapsed.toSeconds());
		}
		
		return SMS.constructMappingsAndUnify(predicateSynthesizer, benchmark, correctPrograms, start, sp);
		
	
		
		
	}
	
	public static SynthesisResult deterministicSMS(Synthesizer predicateSynthesizer, Benchmark benchmark, 
			SynthesisParameters sp, String cvcLocation) throws Exception {	
		

		Verifier verifier = new Verifier(benchmark.getFunctionName(), benchmark.getVariableNames(), null, 
				benchmark.getFunString(), benchmark.getPreTransformAssertionString(),"LIA",
				 null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setSynthType("program");
		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
		
		Instant start = Instant.now();
		
		String[] correctPrograms = null;
		
		String[] extractionVariableNames = new String[benchmark.getVariableNames().length];
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			extractionVariableNames[i] = "var" + (i+1) + ";";
		}
		
		benchmark.setSynthesisVariableNames(extractionVariableNames);
		//String originalAssertionString = benchmark.getAssertionString();

		correctPrograms =  MIUtils.automaticSatisfyingSetConstruction(benchmark);
		//benchmark.setAssertionString(originalAssertionString);
		
	//	//System.out.println("Assembled");
		//benchmark.setSynthesisVariableNames(userSynthesisVariableNames);
		
		/*if (correctPrograms == null) {
			//////System.out.println("Hello");
			correctPrograms = SplitAndConquer.SCGPDiscovery(partialsSynthesizer, benchmark, sp);
		}*/
		
		String[] variables = benchmark.getVariableNames();
		ArrayList<String> variablesList = new ArrayList<>();
		for (int i = 0; i < variables.length; i++) {
			variablesList.add(variables[i]);
		}
		//will only happen on trivial case now, fun
		if (correctPrograms.length == 1) {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			
			String finalProgram = MIUtils.transformProgramFromTempVarsToInvocation(correctPrograms[0], variablesList);
			for (int i = 0; i < benchmark.getVariableNames().length; i++) {
				finalProgram = finalProgram.replace(extractionVariableNames[i], benchmark.getVariableNames()[i]);
			}
			return new SynthesisResult(true,finalProgram,timeElapsed.toSeconds());
		}
		
		
		
		
		
		verifier.setAssertionString(benchmark.getAssertionString());
		
		//OK, we've got all the programs, no reduction as of yet.
		
		//System.out.println("Transformed " + benchmark.getAssertionString());
		
		String functionName = benchmark.getFunctionName();
		String replacementToken = "(replacement_token ";
		
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			replacementToken += " " + benchmark.getVariableNames()[i];
		}
		replacementToken += ")";
		
		
		
		ArrayList<String> fullSatSetList = new ArrayList<>();
		ArrayList<String> reducedSatSetList = new ArrayList<>();
		for (int i =  0; i < correctPrograms.length; i++) {
			fullSatSetList.add(correctPrograms[i]);
			reducedSatSetList.add(correctPrograms[i]);
		}
		
		String[] reducedArray = verifier.MIReduceToNecessarySet(fullSatSetList, null);
		reducedSatSetList.clear();
		for (int i = 0; i < reducedArray.length; i++) {
			reducedSatSetList.add(reducedArray[i]);
		}
		
		ArrayList<String> fullNonItes =  InterchangeableUtils.programsListWithoutITEs(fullSatSetList);
		ArrayList<String> fullItes = InterchangeableUtils.programsListJustITEs(fullSatSetList);
		ArrayList<String> efficientItes = InterchangeableUtils.programsListJustITEs(reducedSatSetList); 

		
		//below makes sure we have all the ites in efficientItes, but the most likely ones are up front.
		for (String s : fullItes) {
			if (!efficientItes.contains(s)) {
				efficientItes.add(s);
			}
		}
		
		
		//means this 
		//System.out.println("Original: " + originalAssertionString);
		
		ArrayList<String> principalPermutations = new ArrayList<>();
		
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			principalPermutations.add(benchmark.getVariableNames()[i]);
		}
		
		ArrayList<String> miPrePrograms = new ArrayList<>();
		ArrayList<String> miPreMappings = new ArrayList<>();
		String masterAssertionString = benchmark.getAssertionString();
		
		while(!InterchangeableUtils.checkAllMICompsFalse(functionName, masterAssertionString)) {
			
			ArrayList<String> compStore = new ArrayList<String>();
			
			masterAssertionString = InterchangeableUtils.blockOutNextConjunction(masterAssertionString, replacementToken, functionName, compStore, benchmark);
			
			String checkingAssertionString = masterAssertionString;
			masterAssertionString = InterchangeableUtils.replaceReplacementTokensWithFalse(masterAssertionString, compStore.size());
	
//			System.out.println("Master Edited with falses: " + masterAssertionString);
			
			checkingAssertionString = InterchangeableUtils.makeAllMICompsFalse(functionName, checkingAssertionString);
			checkingAssertionString = InterchangeableUtils.replaceReplacementTokens(checkingAssertionString, compStore);
			
			ArrayList<ArrayList<String>> sortedUFG = InterchangeableUtils.calculateUFGFromComparisons(compStore, functionName, principalPermutations);
			if (!Verifier.verifySetsEquivalentForProp(checkingAssertionString, fullNonItes, fullSatSetList, benchmark)) {
				ArrayList<String> neccItes = InterchangeableUtils.filterToInterchangeableProgramsWithUFG(efficientItes, sortedUFG);
				
				ArrayList<Integer> removedPartials = new ArrayList<>();
				for (int i = 0; i < neccItes.size(); i++) {
					ArrayList<String> prePartials = new ArrayList<>();
					// build out the partials by index, excluding the current one and ones we have already
					// flagged for removal
					for (int j = 0; j < neccItes.size(); j++) {
						//
						if (i != j && !removedPartials.contains(j)) {
							prePartials.add(neccItes.get(j));
						}
					}

					ArrayList<String> prePartialsPlusNonITEs = new ArrayList<>();
					prePartialsPlusNonITEs.addAll(fullNonItes);
					prePartialsPlusNonITEs.addAll(prePartials);

					if(Verifier.verifySetsEquivalentForProp(checkingAssertionString, prePartialsPlusNonITEs, fullSatSetList, benchmark)) {
						removedPartials.add(i);
					}
					
				}

				// now that we have the partials flagged by index for removal, we add only the ones
				// unflagged into final partials to be used for Predicate Synthesis.
				System.out.println("Running through");
				for (int i = 0; i < neccItes.size(); i++) {
					if (!removedPartials.contains(i)) {
						System.out.println("Found one " + neccItes.get(i));
						miPrePrograms.add(neccItes.get(i));
						miPreMappings.add(
						CVCPredicateSynthesizer.synthesizeCompleteMapping(neccItes.get(i), benchmark, checkingAssertionString, cvcLocation));
					}
				}
				
				
			}
			
			
		
			
			
		}
		
		/*ArrayList<String> neccItes = new ArrayList<String>();
		System.out.println("Sanity check");
		System.out.println(maybeItes.get(0));
		System.out.println("Checking String" + checkingAssertionString);
		
		String checker = "(ite (and true (>= x1 x2)) (+ x1 (+ (* 2 x2) (* 3 x3))) (+ x2 (+ (* 2 x1) (* 3 x3))))";
		if (!maybeItes.contains(checker)) {
			System.out.println("Should only be printed once");
		} else {
			System.out.println("Um fuck me");
		}
		for (int i = 0; i < maybeItes.size(); i++) {
			neccItes.add(maybeItes.get(i));
			
			ArrayList<String> neccItesPlusNonITEs = new ArrayList<>();
			neccItesPlusNonITEs.addAll(fullNonItes);
			neccItesPlusNonITEs.addAll(neccItes);

			if(maybeItes.get(i).equals(checker)) {
				System.out.println("Look at the one below in Z3");
			}
			if (Verifier.verifySetsEquivalentForProp(checkingAssertionString, neccItesPlusNonITEs, fullSatSetList, benchmark)) {
				
				System.out.println("Killer program was " + neccItes.get(neccItes.size()-1));
				
				if (!maybeItes.contains(neccItes.get(neccItes.size()-1))) {
					System.out.println("Red alert");
				} else {
					System.out.println("Well that's strange");
				}
				//miPrePrograms.add(efficientItes.get(i));
				//miPreMappings.add(
				//CVCPredicateSynthesizer.synthesizeCompleteMapping(efficientItes.get(i), benchmark, checkingAssertionString, cvcLocation));
				
				//System.out.println("Found one " + efficientItes.get(i));
				break;
			}
			
			System.out.println("Sanity check complete");
			
			
		}
		
		System.out.println("OK it passed the above what is the problem, let's look at necc ITEs");
		
		for (String s : neccItes) {
			System.out.println(s);
		}
		System.out.println("So that was them");
		*/
		
		String[] nonItesArr = new String[fullNonItes.size()];
		
		for (int i = 0; i < fullNonItes.size(); i++) {
			nonItesArr[i] = fullNonItes.get(i);
		}
		
		
		
		//return SMS.detSMSconstructMappingsAndUnify(predicateSynthesizer, benchmark, correctPrograms, start, sp);
		
		
		SynthesisResult sr = SMS.constructMappingsAndUnify(predicateSynthesizer, benchmark, nonItesArr, start, sp);
		
		String finalProgram = "";
		
		if (miPrePrograms.isEmpty()) {
			finalProgram = sr.getProgramFound();
		} else {
			finalProgram = "(ite (or";
			
			for (String s : miPreMappings) {
				finalProgram += " " + s;
			}
			finalProgram += ")\n ";
			
			ArrayList<String> miPreMappingsLastElemRemoved = new ArrayList<>();
			miPreMappingsLastElemRemoved.addAll(miPreMappings);
			miPreMappingsLastElemRemoved.remove(miPreMappings.size()-1);
			
			finalProgram += unifyProgramNoTransform(miPreMappingsLastElemRemoved, miPrePrograms) + "\n";
			
			finalProgram += sr.getProgramFound() + ")";
			
			
			
			
			
			
		}
		
		//sr = SMS.constructMappingsAndUnify(predicateSynthesizer, benchmark, reducedArray, start, sp);
		verifier.setAssertionString(benchmark.getPreTransformAssertionString());

		
		
		/*VerificationResult vr = verifier.verify(sr.getProgramFound());
		if (vr.getStatus() == Status.UNSATISFIABLE) {
			System.out.println("The original version passed");
		} else {
			System.out.println("Yeah idk");
		}*/
		
		 VerificationResult vr = verifier.verify(finalProgram);
		boolean successful = vr.getStatus() == Status.UNSATISFIABLE;
		
		sr.setSuccessful(successful);
		return sr;
		
		
	}
	
private static String unifyProgramNoTransform(ArrayList<String> mappings, ArrayList<String> partials) {
		
		String unifiedProgram = "";
		String closingParentheses = "";
		
		if (partials.size() == 1) {
			return partials.get(0);
		}

		//System.out.println("Number of Mappings " +  mappings.size());
		//System.out.println("Number of Partials " + partials.size());
		
		for (int i = 0; i < partials.size() - 1; i++) {
			//System.out.println("Mappings " + (i+"") + " " + mappings.get(i));
			unifiedProgram += "(ite " + mappings.get(i) + " " + partials.get(i) + " ";
			closingParentheses += ")";
		}

		unifiedProgram += " " + partials.get(partials.size() - 1) + closingParentheses;

		return unifiedProgram;
	}
	
	
	public static String[] directProgramExtraction(Benchmark benchmark) {
		
		ArrayList<String> partials = new ArrayList<>();
		
		Verifier verifier = new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
				null);
		

		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setVariances(benchmark.getInvocations());
		
		ArrayList<String> varianceCalls = new ArrayList<>();
		ArrayList<ArrayList<String>> variances = benchmark.getInvocations();
		if (variances != null) {
			for (ArrayList<String> arr : variances) {
				String fcs = "(" + benchmark.getFunctionName();

				for (String s: arr ) {
					//////System.out.println("variance var : " + s);
					fcs += " " + s;
				}
				fcs += ")";
				//////System.out.println(fcs);
				varianceCalls.add(fcs);
			}
		}
		/*for(ArrayList<String> arr : benchmark.getVariances()) {
			for (String s : arr) {
				////System.out.println(s);
			}
			////System.out.println("Break");
		}*/
		
		String assertionString = benchmark.getAssertionString();
		
		
		for (String s : varianceCalls) {
			assertionString = assertionString.replace(s, "0");
		}
		
		for (int i = 0; i < verifier.getVerVarNames().length; i++) {
			assertionString = assertionString.replace(verifier.getVerVarNames()[i] + " ", verifier.getSynthesisVariableNames()[i] + " ");
			assertionString = assertionString.replace(verifier.getVerVarNames()[i] + ")", verifier.getSynthesisVariableNames()[i] + ")");
		}
		
	//	////System.out.println(assertionString);
		
		HashSet<String> definedFunctionsSet = null;
		if (benchmark.getDefinedFunctionNames() != null) {
			definedFunctionsSet = new HashSet<String>();
			for (int i = 0; i < benchmark.getDefinedFunctionNames().length; i++) {
				//////System.out.println(benchmark.getDefinedFunctionNames()[i].trim());
				definedFunctionsSet.add(benchmark.getDefinedFunctionNames()[i].trim());
			}
		}
		
		//////System.out.println(assertionString);
		Node constraintsAsProg = Node.buildNodeFromProgramString(assertionString, definedFunctionsSet);
		ArrayList<String> correctTerms = constraintsAsProg.extractPossibleIntProgramsPlusMinusOne();
		


		
		//if (variances.size() > 1) {
			//for (int i = 0; i < correctTerms.size(); i++) {
				//correctTerms.set(i, Verifier.transformSIProgramToMI(correctTerms.get(i), variances, verifier.getSynthesisVariableNames()));
		//	}
		//}
		
		/*for (String s : correctTerms) {
			////System.out.println(s);
		}
		////System.out.println(correctTerms.size());*/
		
		if (!verifier.verifyPartials(correctTerms.toArray(new String[correctTerms.size()]), null)) {
			return null;
		}
		

		

		
		ArrayList<Integer> removedPartials = new ArrayList<>();
		for (int i = 0; i < correctTerms.size(); i++) {
			ArrayList<String> prePartials = new ArrayList<>();
			// build out the partials, excluding the current one and ones we have already
			// flagged for removal
			for (int j = 0; j < correctTerms.size(); j++) {
				//
				if (i != j && !removedPartials.contains(j)) {
					prePartials.add(correctTerms.get(j));
				}
			}

			if (verifier.verifyPartials(prePartials.toArray(new String[prePartials.size()]), null)) {
					removedPartials.add(i);
			} 
			
		}

		// now that we have the partials flagged for removal, we add only the ones
		// unflagged into final partials to be used for Predicate Synthesis.
		for (int i = 0; i < correctTerms.size(); i++) {
			if (!removedPartials.contains(i)) {
				partials.add(correctTerms.get(i));
			} else {
				//////System.out.println("Removed " + correctTerms.get(i));
			}
		}

		return partials.toArray(new String[partials.size()]);
	}
	
public static String[] directProgramExtractionRedux(Benchmark benchmark) {
		
		
		/*Verifier verifier = new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
				null);
		

		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setVariances(benchmark.getInvocations());*/
		
		ArrayList<String> varianceCalls = new ArrayList<>();
		ArrayList<ArrayList<String>> variances = benchmark.getInvocations();
		if (variances != null) {
			for (ArrayList<String> arr : variances) {
				String fcs = "(" + benchmark.getFunctionName();

				for (String s: arr ) {
					//////System.out.println("variance var : " + s);
					fcs += " " + s;
				}
				fcs += ")";
				//////System.out.println(fcs);
				varianceCalls.add(fcs);
			}
		}

		String assertionString = benchmark.getAssertionString();
		
		
		for (String s : varianceCalls) {
			assertionString = assertionString.replace(s, "0");
		}

	/*	for (int i = 0; i < verifier.getVerVarNames().length; i++) {
			while (assertionString.contains(" " + verifier.getVerVarNames()[i] + " ")) {
				assertionString = assertionString.replace(" " + 
			verifier.getVerVarNames()[i] + " ", " " + verifier.getSynthesisVariableNames()[i] + " ");
			}
			assertionString = assertionString.replace(verifier.getVerVarNames()[i] + ")", verifier.getSynthesisVariableNames()[i] + ")");
		}*/
		
		
		for (int i = 0; i < benchmark.getVariableNames().length; i++) {
			while (assertionString.contains(" " + benchmark.getVariableNames()[i] + " ")) {
				assertionString = assertionString.replace(" " + 
			benchmark.getVariableNames()[i] + " ", " " + benchmark.getSynthesisVariableNames()[i] + " ");
			}
			assertionString = assertionString.replace(benchmark.getVariableNames()[i] + ")", benchmark.getSynthesisVariableNames()[i] + ")");
		}
		
	//	////System.out.println(assertionString);
		
		HashSet<String> definedFunctionsSet = null;
		if (benchmark.getDefinedFunctionNames() != null) {
			definedFunctionsSet = new HashSet<String>();
			for (int i = 0; i < benchmark.getDefinedFunctionNames().length; i++) {
				//////System.out.println(benchmark.getDefinedFunctionNames()[i].trim());
				definedFunctionsSet.add(benchmark.getDefinedFunctionNames()[i].trim());
			}
		}
		
		////System.out.println(assertionString);
		Node constraintsAsProg = Node.buildNodeFromProgramString(assertionString, definedFunctionsSet);
		//constraintsAsProg.makeLispTree()
		ArrayList<String> correctTerms = constraintsAsProg.extractPossibleIntProgramsPlusMinusOne();
		


		
		/*if (variances.size() > 1) {
			for (int i = 0; i < correctTerms.size(); i++) {
				correctTerms.set(i, Verifier.transformSIProgramToMI(correctTerms.get(i), variances, verifier.getSynthesisVariableNames()));
			}
		}*/
		
		return correctTerms.toArray(new String[correctTerms.size()]);
	}

}
