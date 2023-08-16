package sms.main;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.PriorityQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import sms.benchmark.Benchmark;
import sms.jobs.SCCallable;
import sms.jobs.SCJobResult;
import sms.jobs.SplitAndCoverProgramSynthesis;
import sms.synthesizer.SynthesisParameters;
import sms.synthesizer.Synthesizer;
import sms.utils.Utils;
import sms.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SplitAndCover {
	
	public static String[] SCGPDiscovery(Synthesizer partialsSynthesizer, Benchmark benchmark, SynthesisParameters sp) throws Exception {
		
		boolean extractAdditionalTerms = sp.isExtractAdditionalTerms();
		int maxTerms = sp.getMaxTermExpansions();
		int maxThreads = sp.getMaxThreads();
		int maxAdditionalTermLength = sp.getMaxAdditionalTermLength();
		boolean emulateCEGIS = sp.isEmulateCEGIS();
		long timeout = sp.getTimeout();
		int additionalTermsCap = sp.getAdditionalTermsCap();
		int additionalTermsPerExtraction = sp.getAdditionalTermsPerExtraction();
		
		Instant start = Instant.now();

		PriorityQueue<SplitAndCoverProgramSynthesis> jobsToProcess = new PriorityQueue<>();

		ArrayList<String> correctTerms = new ArrayList<>();
		ArrayList<String> coveringAdditionalTerms = new ArrayList<>();

		ArrayList<AdditionalTerm> additionalTerms = new ArrayList<>();

		boolean firstRun = true;
		SplitAndCoverProgramSynthesis initialJob = new SplitAndCoverProgramSynthesis(null, 2, 0);
		jobsToProcess.add(initialJob);

		boolean keepGoing = true;

		Verifier verifier = new Verifier(benchmark.getFunctionName(),
				benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
				null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setVariances(benchmark.getInvocations());

		while (keepGoing) {

			//////System.out.println("Next loop");
			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(start, end);

			if (timeElapsed.toMinutes() >= timeout) {
				return null;
			}

			ArrayList<String> correctTermsAndAdditionalTermsPreRun = new ArrayList<>();

			ArrayList<String> additionalTermStringsPreRun = retrieveAdditionalTermsStringArrayList(additionalTerms);
			correctTermsAndAdditionalTermsPreRun.addAll(correctTerms);

			for (String term : additionalTermStringsPreRun) {
				if (!correctTermsAndAdditionalTermsPreRun.contains(term)) {
					correctTermsAndAdditionalTermsPreRun.add(term);
				}
			}

			int additionalTermsAdded = 0;

			int jobsAdded = 0;

			ArrayList<Callable<SCJobResult>> callables = new ArrayList<>();
			List<Future<SCJobResult>> futures = null;
			int runsSize = 1;
			


				while (jobsAdded < maxThreads && !jobsToProcess.isEmpty()) {

					SplitAndCoverProgramSynthesis currentJob = jobsToProcess.remove();
					boolean skip = isJobSkippable(verifier, correctTermsAndAdditionalTermsPreRun,
							currentJob.getExtraAssertions());
					
					if (skip) {
						for (String term : additionalTermStringsPreRun) {
							if (!coveringAdditionalTerms.contains(term)) {
								coveringAdditionalTerms.add(term);
							}
						}

					} else {

						jobsAdded++;

						if (emulateCEGIS) {
							correctTerms.clear();
							additionalTerms.clear();
						}
						callables.add(new SCCallable(partialsSynthesizer, benchmark, currentJob,
								correctTerms, retrieveAdditionalTermsStringArrayList(additionalTerms), sp.isVerifySuccess()));

					}

				}
				
				if (callables.size() > 1) {
					ExecutorService exec = Executors.newFixedThreadPool(maxThreads);
					futures = exec.invokeAll(callables);
					//Utils.awaitTerminationAfterShutdown(exec);
					exec.shutdown();
					runsSize = futures.size();

				}

			
			for (int futuresIndex = 0; futuresIndex < runsSize; futuresIndex++) {

				SCJobResult result = null;
				if (callables.size() == 1) {
					result = callables.get(0).call();
				} else {
					result = futures.get(futuresIndex).get();
				}
				
				SplitAndCoverProgramSynthesis currentJob = result.getParentJob();

				if (!result.isSuccessful()) {
					if (result.getChildren() != null) {
						jobsToProcess.add(result.getChildren()[0]);
						jobsToProcess.add(result.getChildren()[1]);

					} else {
						currentJob.incrementRestarts();
						jobsToProcess.add(currentJob);
					}

					// forget about this stuff, just restart with a new job
					if (emulateCEGIS) {
						jobsToProcess.clear();
						jobsToProcess.add(new SplitAndCoverProgramSynthesis(null, 2, 0));
						futuresIndex += futures.size();
						continue;
					}
				}

				// ////System.out.println("Jobs to process size should be " + theoreticalJobSize + "
				// but is " + jobsToProcess.size());

				if (result.isSuccessful()) {
					////System.out.println("Result was successful");
					ArrayList<String> termsExtracted = Utils.extractTerms(result.getProgram(), maxTerms);
					ArrayList<String> termsToAdd = new ArrayList<>();

					////System.out.println("Correct program: " + result.getProgram());
					if (termsExtracted != null) {
						for (String term : termsExtracted) {
							if (!termsToAdd.contains(term) && !coveringAdditionalTerms.contains(term)) {
								termsToAdd.add(term);
							}
						}
					}

					if (termsToAdd.size() > maxTerms || emulateCEGIS || firstRun || termsExtracted == null) {
						////System.out.println("Adding just as program");
						correctTerms.add(result.getProgram());
					} else {
						// correctTerms.add(currentJob.getProgramTree().makeLispTree());
						////System.out.println("Adding correct terms");
						for (String term : termsToAdd) {
							////System.out.println(term);
							if (!correctTerms.contains(term)) {
								correctTerms.add(term);
							}
						}
					}

					ArrayList<String> additionalTermStrings = retrieveAdditionalTermsStringArrayList(additionalTerms);
					for (String term : additionalTermStrings) {
						if (!coveringAdditionalTerms.contains(term)) {
							coveringAdditionalTerms.add(term);
						}
					}


				} else if(extractAdditionalTerms && result.getProgram() != null && !result.getProgram().isBlank()) {
					////System.out.println("Result was unsuccessful, program attempt: " + result.getProgram());
					ArrayList<String> terms = Utils.extractTerms(result.getProgram(), maxTerms);
					//////System.out.println("Terms extracted");
					ArrayList<String> termsToAddStrings = new ArrayList<>();
					ArrayList<AdditionalTerm> termsToAdd = new ArrayList<>();

					ArrayList<String> additionalTermStrings = retrieveAdditionalTermsStringArrayList(additionalTerms);
					if (terms != null) {
						for (String term : terms) {
							// was doing term.length() < 30, getting rid of that and checking
							if (term.length() < maxAdditionalTermLength && !correctTerms.contains(term)
									&& !additionalTermStrings.contains(term) && !termsToAddStrings.contains(term)
									&& additionalTermsAdded < additionalTermsPerExtraction) {
								// ////System.out.println(term);
								termsToAddStrings.add(term);
								termsToAdd.add(new AdditionalTerm(term));
								additionalTermsAdded++;

							}
						}
					}

					if (additionalTerms.size() > additionalTermsCap) {

						Collections.sort(additionalTerms, Collections.reverseOrder());
						int numToRemove = additionalTerms.size() - additionalTermsCap;
						for (int i = 0; i < numToRemove; i++) {

							additionalTerms.remove(additionalTerms.size() - 1);
						}
					}

					additionalTerms.addAll(termsToAdd);

					// ////System.out.println("Additional terms size is " + additionalTerms.size());

				}
				
				firstRun = false;

			}

			ArrayList<String> correctTermsAndAdditionalTerms = new ArrayList<>();
			correctTermsAndAdditionalTerms.addAll(correctTerms);
			for (String term : coveringAdditionalTerms) {
				if (!correctTermsAndAdditionalTerms.contains(term)) {
					correctTermsAndAdditionalTerms.add(term);
				}
			}

			for (String term : retrieveAdditionalTermsStringArrayList(additionalTerms)) {
				if (!correctTermsAndAdditionalTerms.contains(term)) {
					correctTermsAndAdditionalTerms.add(term);
				}
			}

			 ////System.out.println("Checking the following terms");
			for (String s : correctTermsAndAdditionalTerms) {
				////System.out.println(s);
			}

			keepGoing = !verifier.verifyPartials(
					correctTermsAndAdditionalTerms.toArray(new String[correctTermsAndAdditionalTerms.size()]), null);



			if (!keepGoing) {

				for (String term : retrieveAdditionalTermsStringArrayList(additionalTerms)) {
					if (!coveringAdditionalTerms.contains(term)) {
						coveringAdditionalTerms.add(term);
					}
				}

			}

		}

		// we have all the terms we need, add any additional terms to correctTerms and
		// reduce the set.
		for (String term : coveringAdditionalTerms) {
			if (!correctTerms.contains(term)) {
				correctTerms.add(term);
			}
		}

		for (int i = 0; i < correctTerms.size(); i++) {
			////System.out.println("Term " + (i + 1) + ":" + correctTerms.get(i));
		}
		
		return verifier.reduceToNecessarySet(correctTerms);
		
		/*
		// The following loop eliminates any overlapping terms to prevent
		// unnecessary work. Similar operation was used in original STUN GP.
		// Basically, remove one at a time and see if the problem is still unsat and
		// thus
		// the terms still covering. If it is unsat, add the term to the removedPartials
		// and
		// exclude it going forward.
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
				////System.out.println("Removed " + correctTerms.get(i));
			}
		}

		return partials.toArray(new String[partials.size()]);*/

	}
	
	private static boolean isJobSkippable(Verifier verifier, ArrayList<String> correctTermsAndAdditionalTermsPreRun, String[] extraAssertions) {
		return verifier.verifyPartials(
				correctTermsAndAdditionalTermsPreRun
						.toArray(new String[correctTermsAndAdditionalTermsPreRun.size()]),
				extraAssertions);

	}
	
	private static ArrayList<String> retrieveAdditionalTermsStringArrayList(ArrayList<AdditionalTerm> additionalTerms) {
		ArrayList<String> terms = new ArrayList<>();
		for (AdditionalTerm term : additionalTerms) {
			terms.add(term.getTerm());
		}

		return terms;

	}
	
}
