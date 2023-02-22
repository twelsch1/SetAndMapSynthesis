package bcs.main;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.HashSet;

import bcs.benchmark.Benchmark;
import bcs.programNode.Node;
import bcs.synthesizer.SynthesisParameters;
import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
import bcs.verification.Verifier;

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
		String[] correctPrograms = SplitAndConquer.SCGPDiscovery(synthesizer, benchmark, sp);
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		} else {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			return new SynthesisResult(true,correctPrograms[0],timeElapsed.toSeconds());
		}
	}
	
	public static SynthesisResult runPartialThenPredicateSynthesis(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark) throws Exception {	
		SynthesisParameters sp = new SynthesisParameters();
		return runPartialThenPredicateSynthesis(partialsSynthesizer,predicateSynthesizer,benchmark,sp);
	}
	
	public static SynthesisResult runPartialThenPredicateSynthesis(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark, 
			SynthesisParameters sp) throws Exception {	
		
		Instant start = Instant.now();

		String[] correctPrograms = SplitAndConquer.SCGPDiscovery(partialsSynthesizer, benchmark, sp);
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		}
		
		if (correctPrograms.length == 1) {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			return new SynthesisResult(true,correctPrograms[0],timeElapsed.toSeconds());
		}
		
		return BCS.synthesizePredicates(predicateSynthesizer, benchmark, correctPrograms, start, sp);
		
	
		
		
	}
	
	public static SynthesisResult runProgramExtractionThenPredicateSynthesis(Synthesizer partialsSynthesizer, Synthesizer predicateSynthesizer, Benchmark benchmark, 
			SynthesisParameters sp) throws Exception {	
		

		
		Instant start = Instant.now();
		
		String[] correctPrograms = null;
		correctPrograms = directProgramExtraction(benchmark);
		
		/*if (correctPrograms == null) {
			//System.out.println("Hello");
			correctPrograms = SplitAndConquer.SCGPDiscovery(partialsSynthesizer, benchmark, sp);
		}*/
		
		if (correctPrograms == null) {
			return new SynthesisResult(false,"",3600);
		}
		
		if (correctPrograms.length == 1) {
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);
			return new SynthesisResult(true,correctPrograms[0],timeElapsed.toSeconds());
		}
		
		return BCS.synthesizePredicates(predicateSynthesizer, benchmark, correctPrograms, start, sp);
		
	
		
		
	}
	
	private static String[] directProgramExtraction(Benchmark benchmark) {
		
		ArrayList<String> partials = new ArrayList<>();
		
		Verifier verifier = new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
				null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setVariances(benchmark.getVariances());
		
		ArrayList<String> varianceCalls = new ArrayList<>();
		ArrayList<ArrayList<String>> variances = benchmark.getVariances();
		if (variances != null) {
			for (ArrayList<String> arr : variances) {
				String fcs = "(" + benchmark.getFunctionName();

				for (String s: arr ) {
					//System.out.println("variance var : " + s);
					fcs += " " + s;
				}
				fcs += ")";
				//System.out.println(fcs);
				varianceCalls.add(fcs);
			}
		}
		/*for(ArrayList<String> arr : benchmark.getVariances()) {
			for (String s : arr) {
				System.out.println(s);
			}
			System.out.println("Break");
		}*/
		
		String assertionString = benchmark.getAssertionString();
		
		
		for (String s : varianceCalls) {
			assertionString = assertionString.replace(s, "0");
		}
		
		for (int i = 0; i < verifier.getVerVarNames().length; i++) {
			assertionString = assertionString.replace(verifier.getVerVarNames()[i] + " ", verifier.getTempVarNames()[i] + " ");
			assertionString = assertionString.replace(verifier.getVerVarNames()[i] + ")", verifier.getTempVarNames()[i] + ")");
		}
		
	//	System.out.println(assertionString);
		
		HashSet<String> definedFunctionsSet = null;
		if (benchmark.getDefinedFunctionNames() != null) {
			definedFunctionsSet = new HashSet<String>();
			for (int i = 0; i < benchmark.getDefinedFunctionNames().length; i++) {
				System.out.println(benchmark.getDefinedFunctionNames()[i].trim());
				definedFunctionsSet.add(benchmark.getDefinedFunctionNames()[i].trim());
			}
		}
		
		System.out.println(assertionString);
		Node constraintsAsProg = Node.buildNodeFromProgramString(assertionString, definedFunctionsSet);
		ArrayList<String> correctTerms = constraintsAsProg.extractPossibleIntProgramsPlusMinusOne();
		


		
		if (variances.size() > 1) {
			for (int i = 0; i < correctTerms.size(); i++) {
				correctTerms.set(i, Verifier.transformSIProgramToMI(correctTerms.get(i), variances, verifier.getTempVarNames()));
			}
		}
		
		/*for (String s : correctTerms) {
			System.out.println(s);
		}
		System.out.println(correctTerms.size());*/
		
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
				//System.out.println("Removed " + correctTerms.get(i));
			}
		}

		return partials.toArray(new String[partials.size()]);
	}

}
