package sms.main;

import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import com.microsoft.z3.Context;
import com.microsoft.z3.Status;

import sms.benchmark.Benchmark;
import sms.branchwisePredicateSynthesis.BranchwisePredicateSynthesis;
import sms.branchwisePredicateSynthesis.helpers.BPSCallable;
import sms.branchwisePredicateSynthesis.helpers.BPSJobResult;
import sms.multipleInvocation.MIUtils;
import sms.synthesizer.SynthesisParameters;
import sms.synthesizer.SynthesisResult;
import sms.synthesizer.Synthesizer;
import sms.verification.VerificationCallParameters;
import sms.verification.VerificationResult;
import sms.verification.Verifier;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SMS {

	public static SynthesisResult constructMappingsAndUnify(Synthesizer predicateSynthesizer, Benchmark benchmark, 
			String[] partials, Instant start,
			SynthesisParameters sp) throws Exception {	
		

		
	
		//Edge cases where end user is misusing functions, can't be reached if using SynthesisMethods functions
		if (partials == null) {
			throw new Exception("No partial programs provided for predicateSynthesis");
		}
		
		if (partials.length == 1) {
			throw new Exception("Partial programs must be greater than 1");
		}
		
		/*////System.out.println("Partials are");
		for (int i = 0; i < partials.length; i++) {
			////System.out.println(partials[i]);
		}*/
		//Retrieve variables from SynthesisParameters
		long timeout = sp.getTimeout();
		int maxThreads = sp.getMaxThreads();
		boolean emulateSTUN = sp.isEmulateSTUN();
		boolean skip = sp.isSkipToRepair();
		boolean verifySuccess = sp.isVerifySuccess();
		
		//synthesis is assumed to be unsuccessful until verification of final program is confirmed
		boolean successful = false;

		//Set up the verifier that we use to confirm final program is correct
		Verifier verifier = new Verifier(benchmark.getFunctionName(), benchmark.getVariableNames(), null, 
				benchmark.getFunString(), benchmark.getAssertionString(),"LIA",
				 null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setSynthType("program");
		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
		
		//Initial attempt at synthesis, returns a set of jobs that have correct mappings or null if synthesis times out
		ArrayList<BranchwisePredicateSynthesis> completedJobs = synthesizeFinalProgram(predicateSynthesizer, benchmark, partials, maxThreads, start, timeout, emulateSTUN,skip, "",
				sp.getPctOfPositives(),verifySuccess, sp.getBranchwiseMode());
		
		//If completedJobs is null means we timed out, return success as false, with time taken as timeout and no program found
		if (completedJobs == null) {
			return new SynthesisResult(false,"",timeout*60);
		}
		
		//Build the program to be checked from the completedJobs which among other things contains the partial and corresponding mapping
		String finalProgram = buildUnifiedProgram(completedJobs, benchmark);
		////System.out.println(finalProgram);
		/*for (int i = 0; i < verifier.getVerVarNames().length; i++) {
			finalProgram = finalProgram.replace(verifier.getSynthesisVariableNames()[i], verifier.getVerVarNames()[i]);
		}*/
		
		////System.out.println(finalProgram);
		/*
		String[] functionVariables = benchmark.getFunctionVariables();
		ArrayList<String> firstInvocation = benchmark.getInvocations().get(0);
		for (int i = 0; i < functionVariables.length; i++) {
			finalProgram = finalProgram.replace(functionVariables[i] + " ", "var" + i + "; " );
			finalProgram = finalProgram.replace(functionVariables[i] + ")", "var" + i + ";)" );
		}
		
		////System.out.println(finalProgram);
		for (int i = 0; i < firstInvocation.size(); i++) {
			finalProgram = finalProgram.replace("var" + i + ";", firstInvocation.get(i));
		}
		
		////System.out.println(finalProgram);*/
		
		//Use try with resources to kick off new Z3 context, ensures it is closed after the try
		try(Context ctx = new Context()) {
			
			VerificationResult vr = null;
			boolean done = false;

			//Add the context to verification call parameters 
			VerificationCallParameters vcp = new VerificationCallParameters();
			vcp.setContext(ctx);
			
			//////System.out.println("Verifying synthesized program");
			//check if the final program is correct, if it is, set done to true
			//////System.out.println("Final program to be verified: " + finalProgram);
			System.out.println("Here is the first final program " + finalProgram);
	
			
			vr = verifier.verify(finalProgram, vcp);
			done = vr.getStatus() == Status.UNSATISFIABLE;
			done = true;
			
			if (done) {
				//set successful to true, move onto returning result
				successful = true;
			} else {
				////System.out.println("Following program didnt work");
				////System.out.println(finalProgram);
				////System.out.println("Repair Procedure initiated ");
				//Build the repairConstraint, representing the space where ties need to be resolved
				String repairConstraint = buildRepairConstraint(completedJobs);

				//perform synthesis again on the space covered by repairConstraint and with omitDistinctness set to true
				//to ensure soundness regarldess of parallelism
				completedJobs = synthesizeFinalProgram(predicateSynthesizer, benchmark, partials, maxThreads, start, timeout, emulateSTUN, true, repairConstraint,
						sp.getPctOfPositives(),verifySuccess, sp.getBranchwiseMode());
				
				//Means we found no solution, return unsuccessful with max timeout
				if (completedJobs == null) {
					return new SynthesisResult(false,"",timeout*60);
				}
				
				//build the program that is correct when repairConstraint is true
				String leftProgram = buildUnifiedProgram(completedJobs, benchmark);
				
				//Unify the original synthesis attempt, with the program that is correct given repairConstraint on the
				//left hand side and the original program being on the right hand side.
				finalProgram = "(ite " + repairConstraint + " " + leftProgram + " " + finalProgram + ")";
				
				for (int i = 0; i < verifier.getVerVarNames().length; i++) {
					finalProgram = finalProgram.replace(verifier.getSynthesisVariableNames()[i], verifier.getVerVarNames()[i]);
				}

				//Confirm it is correct. It should be at this stage, if not there is a bug.
				vr = verifier.verify(finalProgram, vcp);
				
				if (vr.getStatus() == Status.UNSATISFIABLE) {
					//program was correct, set successful to true
					successful = true;
				} else {

					////System.out.println(vr.getStatus());
					//program was incorrect, print the program that failed
					////System.out.println("Following program wasn't correct: ");
					////System.out.println(finalProgram);
				}
				
			}
		} catch (Exception e) {
			e.printStackTrace();
			////System.out.println(e.getMessage());
		} 
		
		//check how long it all took, then return the result
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);
		
		
		String[] variables = benchmark.getVariableNames();
		ArrayList<String> variablesList = new ArrayList<>();
		for (int i = 0; i < variables.length; i++) {
			variablesList.add(variables[i]);
		}
		
		finalProgram = MIUtils.transformProgramFromTempVarsToInvocation(finalProgram, variablesList);
		return new SynthesisResult(successful,finalProgram,timeElapsed.toSeconds());
	
		
		
	}
	
	
	public static SynthesisResult detSMSconstructMappingsAndUnify(Synthesizer predicateSynthesizer, Benchmark benchmark, 
			String[] partials, Instant start,
			SynthesisParameters sp) throws Exception {	
		

		
	
		//Edge cases where end user is misusing functions, can't be reached if using SynthesisMethods functions
		if (partials == null) {
			throw new Exception("No partial programs provided for predicateSynthesis");
		}
		
		if (partials.length == 1) {
			throw new Exception("Partial programs must be greater than 1");
		}
		
		/*////System.out.println("Partials are");
		for (int i = 0; i < partials.length; i++) {
			////System.out.println(partials[i]);
		}*/
		//Retrieve variables from SynthesisParameters
		long timeout = sp.getTimeout();
		int maxThreads = sp.getMaxThreads();
		boolean emulateSTUN = sp.isEmulateSTUN();
		boolean skip = sp.isSkipToRepair();
		boolean verifySuccess = sp.isVerifySuccess();
		
		//synthesis is assumed to be unsuccessful until verification of final program is confirmed
		boolean successful = false;

		//Set up the verifier that we use to confirm final program is correct
		Verifier verifier = new Verifier(benchmark.getFunctionName(), benchmark.getVariableNames(), null, 
				benchmark.getFunString(), benchmark.getAssertionString(),"LIA",
				 null);
		verifier.setDefinedFunctions(benchmark.getDefinedFunctions());
		verifier.setSynthType("program");
		verifier.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
		
		//Initial attempt at synthesis, returns a set of jobs that have correct mappings or null if synthesis times out
		ArrayList<BranchwisePredicateSynthesis> completedJobs = detSynthesizeFinalProgram(predicateSynthesizer, benchmark, partials, maxThreads, start, timeout, emulateSTUN,skip, "",
				sp.getPctOfPositives(),verifySuccess, sp.getBranchwiseMode());
		
		//If completedJobs is null means we timed out, return success as false, with time taken as timeout and no program found
		if (completedJobs == null) {
			return new SynthesisResult(false,"",timeout*60);
		}
		
		
		
		String finalProgram = SMS.inductiveUnification(completedJobs, verifier, benchmark);
		
		//Use try with resources to kick off new Z3 context, ensures it is closed after the try
		try(Context ctx = new Context()) {
			
			
			VerificationResult vr = null;

			//Add the context to verification call parameters 
			VerificationCallParameters vcp = new VerificationCallParameters();
			vcp.setContext(ctx);

	
			
			vr = verifier.verify(finalProgram, vcp);
			successful = vr.getStatus() == Status.UNSATISFIABLE;
			
		} catch (Exception e) {
			e.printStackTrace();
			////System.out.println(e.getMessage());
		} 
		
		//check how long it all took, then return the result
		Instant end = Instant.now();
		Duration timeElapsed = Duration.between(start, end);
		
		
		String[] variables = benchmark.getVariableNames();
		ArrayList<String> variablesList = new ArrayList<>();
		for (int i = 0; i < variables.length; i++) {
			variablesList.add(variables[i]);
		}
		
		finalProgram = MIUtils.transformProgramFromTempVarsToInvocation(finalProgram, variablesList);
		return new SynthesisResult(successful,finalProgram,timeElapsed.toSeconds());

	
		
		
	}
	
	private static String buildUnifiedProgram(ArrayList<BranchwisePredicateSynthesis> completedJobs, Benchmark benchmark) {
		
		if (completedJobs == null) {
			return null;
		}
		
		String[] functionVariables = benchmark.getVariableNames();
		
		ArrayList<String> variablesList = new ArrayList<>();
		for (int i = 0; i < functionVariables.length; i++) {
			variablesList.add(functionVariables[i]);
		}

		
		ArrayList<String> mappings = new ArrayList<>();
		ArrayList<String> partials = new ArrayList<>();
		for (int i = 0; i < completedJobs.size(); i++) {
			mappings.add(completedJobs.get(i).getCorrectMapping());
			partials.add(completedJobs.get(i).getTargetPartial());
		}
		
		for (int i = 0; i < mappings.size(); i++) {
			mappings.set(i, MIUtils.transformProgramFromTempVarsToInvocation(mappings.get(i), variablesList));
		}


		String unifiedProgram = "";
		String closingParentheses = "";
		
		

		
		
		for (int i = 0; i < completedJobs.size() - 1; i++) {
			unifiedProgram += "(ite " + mappings.get(i) + " " + partials.get(i) + " ";
			closingParentheses += ")";
		}

		unifiedProgram += " " + partials.get(completedJobs.size() - 1) + closingParentheses;

		return unifiedProgram;
	}
	
	
	public static String detSMSbuildUnifiedProgram(ArrayList<String> mappings, ArrayList<String> partials, Benchmark benchmark) {
		

		
		String[] functionVariables = benchmark.getVariableNames();
		
		ArrayList<String> variablesList = new ArrayList<>();
		for (int i = 0; i < functionVariables.length; i++) {
			variablesList.add(functionVariables[i]);
		}

		

		
		for (int i = 0; i < mappings.size(); i++) {
			mappings.set(i, MIUtils.transformProgramFromTempVarsToInvocation(mappings.get(i), variablesList));
		}


		String unifiedProgram = "";
		String closingParentheses = "";
		
		

		
		
		for (int i = 0; i < partials.size() - 1; i++) {
			unifiedProgram += "(ite " + mappings.get(i) + " " + partials.get(i) + " ";
			closingParentheses += ")";
		}

		unifiedProgram += " " + partials.get(partials.size() - 1) + closingParentheses;

		return unifiedProgram;
	}
	
	private static String buildRepairConstraint(ArrayList<BranchwisePredicateSynthesis> completedJobs) {
		String unifiedProgram = "";
		String closingParentheses = "";

		if (completedJobs == null) {
			return null;
		}
		
		for (int i = 0; i < completedJobs.size() - 1; i++) {
			unifiedProgram += "(ite " + completedJobs.get(i).getCorrectMapping() + " false ";
			closingParentheses += ")";
		}

		unifiedProgram += " true"  + closingParentheses;

		return unifiedProgram;
	}
	
	private static ArrayList<BranchwisePredicateSynthesis> synthesizeFinalProgram(Synthesizer predicateSynthesizer, Benchmark benchmark, String[] correctPrograms, 
			 int maxThreads, Instant beginning, long timeout, boolean emulateSTUN, boolean repair,
			 String repairConstraint, double pctOfPositives,boolean verifySuccess, String branchwiseMode) throws Exception {
		if (maxThreads > 1) {
			return synthesizeFinalProgramParallel(predicateSynthesizer, benchmark, correctPrograms, maxThreads, beginning, timeout, emulateSTUN, repair, repairConstraint, pctOfPositives,verifySuccess, branchwiseMode);
		} else {
			return synthesizeFinalProgramSerial(predicateSynthesizer, benchmark, correctPrograms, beginning, timeout, emulateSTUN, pctOfPositives,verifySuccess, branchwiseMode);
		}
		
	}
	
	private static ArrayList<BranchwisePredicateSynthesis> detSynthesizeFinalProgram(Synthesizer predicateSynthesizer, Benchmark benchmark, String[] correctPrograms, 
			 int maxThreads, Instant beginning, long timeout, boolean emulateSTUN, boolean repair,
			 String repairConstraint, double pctOfPositives,boolean verifySuccess, String branchwiseMode) throws Exception {
		if (maxThreads > 1) {
			return synthesizeFinalProgramParallel(predicateSynthesizer, benchmark, correctPrograms, maxThreads, beginning, timeout, emulateSTUN, repair, repairConstraint, pctOfPositives,verifySuccess, branchwiseMode);
		} else {
			return detSynthesizeFinalProgramSerial(predicateSynthesizer, benchmark, correctPrograms, beginning, timeout, emulateSTUN, pctOfPositives,verifySuccess, branchwiseMode);
		}
		
	}
	
	private static ArrayList<BranchwisePredicateSynthesis> synthesizeFinalProgramParallel(Synthesizer predicateSynthesizer, Benchmark benchmark, String[] correctPrograms, 
			 int maxThreads, Instant beginning, long timeout, boolean emulateSTUN, boolean repair,
			  String repairConstraint, double pctOfPositives, boolean verifySuccess, String branchwiseMode) throws InterruptedException, ExecutionException {
		
		PriorityQueue<BranchwisePredicateSynthesis> predicateJobs = new PriorityQueue<>();
		ArrayList<BranchwisePredicateSynthesis> completedJobs = new ArrayList<>();
		HashMap<String,BranchwisePredicateSynthesis> inProcessJobs = new HashMap<>();
		ArrayList<String> globalConstraints = new ArrayList<>();
		int numCorrectJobs = 0;
		
		
		
		for (int i = 0; i < correctPrograms.length; i++) {
			BranchwisePredicateSynthesis rmpj = new BranchwisePredicateSynthesis(
			correctPrograms[i]);
			//rmpj.run
			//rmpj.run
			if (repair) {
				rmpj.setRepairConstraint(repairConstraint);
				rmpj.setOmitDistinctness(true);
			}
			
			predicateJobs.add(rmpj);
			


		}

		
		int correctPredsNeeded = predicateJobs.size()-1;

		
		ExecutorService exec = Executors.newFixedThreadPool(maxThreads);
		
		CompletionService<BPSJobResult> ecs
	         = new ExecutorCompletionService<BPSJobResult>(exec);
		
		try {
			
			while (numCorrectJobs < correctPredsNeeded) {
				
				Instant end = Instant.now();
				Duration timeElapsed = Duration.between(beginning, end);

				// timeout if we go over the timeout in minutes
				if (timeElapsed.toMinutes() >= timeout) {
					return null;
				}
				
				
				//If inProcessJobs is the max threads OR we have no more jobs to submit, then wait for the next result.
				//Otherwise, we submit a new job
				if (inProcessJobs.size() == maxThreads || predicateJobs.isEmpty()) {
					BPSJobResult r = ecs.take().get();
					BranchwisePredicateSynthesis job = r.getJob();
					inProcessJobs.remove(job.getTargetPartial());
					if (job.isSynthesisFinished()) {
						completedJobs.add(job);
						//////System.out.println("Added partial " + job.getTargetPartial());
						//////System.out.println("Mapping " + job.getCorrectMapping());
						numCorrectJobs++;
					} else {
						
						// if we are doing emulateSTUN, start with a fresh job to restart from scratch,
						// like the original STUN. Otherwise, add the now updated job.
						if (emulateSTUN) {
							predicateJobs.add(new BranchwisePredicateSynthesis(job.getTargetPartial()));
						} else {
							predicateJobs.add(job);
						}
					}

					if (numCorrectJobs == correctPredsNeeded) {
						
						//shutdown pool and then any other thread that is running other than this one for good measure
						exec.shutdownNow();
	

						Set<Thread> threadSet = Thread.getAllStackTraces().keySet();
						for (Thread thread : threadSet) {

							//Don't interrupt the controlling thread
							if (Thread.currentThread() != thread) {
								thread.interrupt();
							}
						}
						
						//give a bit of time to end gracefully before we move on, should end well before this
						exec.awaitTermination(5, TimeUnit.SECONDS);
						break;
					}
				} else {

					BranchwisePredicateSynthesis job = predicateJobs.remove();


					job.setRemainingTerms(buildRemainingTerms(predicateJobs, inProcessJobs));

					ArrayList<BranchwisePredicateSynthesis> allJobs = new ArrayList<>();
					allJobs.addAll(predicateJobs);
					allJobs.addAll(completedJobs);

					for (BranchwisePredicateSynthesis rmpj : inProcessJobs.values()) {
						allJobs.add(rmpj);
					}

					allJobs.add(job);

					String globalConstraintsString = "";
	
					globalConstraints = buildGlobalConstraints(allJobs, allJobs.size() - 1);

					if (!globalConstraints.isEmpty()) {
						globalConstraintsString = String.join(",,,",
								globalConstraints.toArray(new String[globalConstraints.size()]));
					}

					inProcessJobs.put(job.getTargetPartial(), job);
					ecs.submit(new BPSCallable(job, predicateSynthesizer, benchmark, globalConstraintsString, pctOfPositives,verifySuccess, numCorrectJobs, branchwiseMode));
				}


			}
			
			for (BranchwisePredicateSynthesis job : inProcessJobs.values()) {
				completedJobs.add(job);
			}

			//////System.out.println("Finished synthesizing predicates, onto unification and final verification");
		} finally {
			exec.shutdownNow();
		}
		
		return completedJobs;
		

			
		
	}
		
	private static ArrayList<BranchwisePredicateSynthesis> synthesizeFinalProgramSerial(Synthesizer predicateSynthesizer, Benchmark benchmark, String[] correctPrograms, 
			  Instant beginning, long timeout, boolean emulateSTUN, double pctOfPositives, boolean verifySuccess, String branchwiseMode) throws Exception {
		PriorityQueue<BranchwisePredicateSynthesis> predicateJobs = new PriorityQueue<>();
		ArrayList<BranchwisePredicateSynthesis> completedJobs = new ArrayList<>();
		ArrayList<String> globalConstraints = new ArrayList<>();

		int numCorrectJobs = 0;
		
		for (int i = 0; i < correctPrograms.length; i++) {
			BranchwisePredicateSynthesis rmpj = new BranchwisePredicateSynthesis(
					correctPrograms[i]);
			//rmpj.set
			rmpj.setFirstPriority(i);
			predicateJobs.add(rmpj);
		}
		
		
		int correctPredsNeeded = predicateJobs.size()-1;

		
		

		while (numCorrectJobs < correctPredsNeeded) {

			//////System.out.println("New loop around");

			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(beginning, end);

			// timeout if we go over the timeout in minutes
			if (timeElapsed.toMinutes() > timeout) {
				return null;
			}

			BranchwisePredicateSynthesis job = predicateJobs.remove();

			job.setRemainingTerms(buildRemainingTerms(predicateJobs, null));


			ArrayList<BranchwisePredicateSynthesis> allJobs = new ArrayList<>();
			allJobs.addAll(predicateJobs);
			allJobs.addAll(completedJobs);

			allJobs.add(job);

			String globalConstraintsString = "";

			globalConstraints = buildGlobalConstraints(allJobs, allJobs.size() - 1);

			if (!globalConstraints.isEmpty()) {
				globalConstraintsString = String.join(",,,",
						globalConstraints.toArray(new String[globalConstraints.size()]));
			}

			Verifier ver = new Verifier(benchmark.getFunctionName(),
					benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
					null);

			ver.setDefinedFunctions(benchmark.getDefinedFunctions());
			ver.setPctOfPositives(pctOfPositives);
			ver.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
			
			if (!globalConstraintsString.isEmpty()) {
				ver.setGlobalConstraints(globalConstraintsString.split(",,,"));
			}
			ver.setSynthType("predicate");
			
			job.run(ver, predicateSynthesizer, verifySuccess, numCorrectJobs, branchwiseMode);

			if (job.isSynthesisFinished()) {
				completedJobs.add(job);
				////System.out.println("Added partial " + job.getTargetPartial());
				////System.out.println("Mapping " + job.getCorrectMapping());
				numCorrectJobs++;
			} else {
				// if we are doing emulateSTUN, start with a fresh job to restart from scratch,
				// like the original STUN. Otherwise, add the now updated job.
				if (emulateSTUN) {
					BranchwisePredicateSynthesis freshJob = new BranchwisePredicateSynthesis(job.getTargetPartial());
					predicateJobs.add(freshJob);
				} else {
					predicateJobs.add(job);
				}
			}
		}

		completedJobs.add(predicateJobs.remove());
			
//		////System.out.println("Finished synthesizing predicates, onto unification and final verification");

		return completedJobs;
		

		
		
	}
		
	private static ArrayList<BranchwisePredicateSynthesis> detSynthesizeFinalProgramSerial(Synthesizer predicateSynthesizer, Benchmark benchmark, String[] correctPrograms, 
			  Instant beginning, long timeout, boolean emulateSTUN, double pctOfPositives, boolean verifySuccess, String branchwiseMode) throws Exception {
		PriorityQueue<BranchwisePredicateSynthesis> predicateJobs = new PriorityQueue<>();
		ArrayList<BranchwisePredicateSynthesis> completedJobs = new ArrayList<>();
		ArrayList<String> globalConstraints = new ArrayList<>();

		int numCorrectJobs = 0;
		//System.out.println("Number of programs " + correctPrograms.length);
		for (int i = 0; i < correctPrograms.length; i++) {
			BranchwisePredicateSynthesis rmpj = new BranchwisePredicateSynthesis(
					correctPrograms[i]);
			//rmpj.set
			rmpj.setFirstPriority(i);
			predicateJobs.add(rmpj);
		}
		
		
		int correctPredsNeeded = predicateJobs.size();

		
		

		while (numCorrectJobs < correctPredsNeeded) {

			//////System.out.println("New loop around");

			Instant end = Instant.now();
			Duration timeElapsed = Duration.between(beginning, end);

			// timeout if we go over the timeout in minutes
			if (timeElapsed.toMinutes() > timeout) {
				return null;
			}

			BranchwisePredicateSynthesis job = predicateJobs.remove();

			job.setRemainingTerms(buildRemainingTerms(predicateJobs, null));


			ArrayList<BranchwisePredicateSynthesis> allJobs = new ArrayList<>();
			allJobs.addAll(predicateJobs);
			allJobs.addAll(completedJobs);

			allJobs.add(job);

			String globalConstraintsString = "";

			globalConstraints = buildGlobalConstraints(allJobs, allJobs.size() - 1);

			if (!globalConstraints.isEmpty()) {
				globalConstraintsString = String.join(",,,",
						globalConstraints.toArray(new String[globalConstraints.size()]));
			}

			Verifier ver = new Verifier(benchmark.getFunctionName(),
					benchmark.getVariableNames(), null, benchmark.getFunString(), benchmark.getAssertionString(), "LIA",
					null);

			ver.setDefinedFunctions(benchmark.getDefinedFunctions());
			ver.setPctOfPositives(pctOfPositives);
			ver.setSynthesisVariableNames(benchmark.getSynthesisVariableNames());
			
			if (!globalConstraintsString.isEmpty()) {
				ver.setGlobalConstraints(globalConstraintsString.split(",,,"));
			}
			ver.setSynthType("predicate");
			
			job.run(ver, predicateSynthesizer, verifySuccess, numCorrectJobs, branchwiseMode);

			if (job.isSynthesisFinished()) {
				completedJobs.add(job);
				////System.out.println("Added partial " + job.getTargetPartial());
				////System.out.println("Mapping " + job.getCorrectMapping());
				numCorrectJobs++;
			} else {
				// if we are doing emulateSTUN, start with a fresh job to restart from scratch,
				// like the original STUN. Otherwise, add the now updated job.
				if (emulateSTUN) {
					BranchwisePredicateSynthesis freshJob = new BranchwisePredicateSynthesis(job.getTargetPartial());
					predicateJobs.add(freshJob);
				} else {
					predicateJobs.add(job);
				}
			}
		}

		//completedJobs.add(predicateJobs.remove());
			
//		////System.out.println("Finished synthesizing predicates, onto unification and final verification");

		return completedJobs;
		

		
		
	}
		
	private static ArrayList<String> buildGlobalConstraints(ArrayList<BranchwisePredicateSynthesis> jobs, int includeIndex) {
		ArrayList<String> globalConstraints = new ArrayList<>();
		for (int i = 0; i < jobs.size(); i++) {
			BranchwisePredicateSynthesis job = jobs.get(i);

			if (job.isSynthesisFinished()) {
				globalConstraints.add(job.getCorrectMapping());
			} else if (i == includeIndex) {
				//globalConstraints.addAll(job.getClauses());
			}
				
			
		}
		
		return globalConstraints;
	}
	
	private static ArrayList<String> buildRemainingTerms(PriorityQueue<BranchwisePredicateSynthesis> jobs, 
			HashMap<String, BranchwisePredicateSynthesis> inProcessJobs) {
		ArrayList<String> remainingTerms = new ArrayList<>();
		for (BranchwisePredicateSynthesis job : jobs) {
			remainingTerms.add(job.getTargetPartial());
		}
		
		if (inProcessJobs != null) {
			for (String partial : inProcessJobs.keySet()) {
				remainingTerms.add(partial);
			}
		}
		

		return remainingTerms;
	}
	
	private static String inductiveUnification(ArrayList<BranchwisePredicateSynthesis> completedJobs, Verifier verifier, Benchmark benchmark) {
		int iteIndex = determineITEIndex(completedJobs);
		ArrayList<BranchwisePredicateSynthesis> nonIteJobs = new ArrayList<>();
		ArrayList<BranchwisePredicateSynthesis> iteJobs = new ArrayList<>();
		ArrayList<String> mappings = new ArrayList<String>();
		ArrayList<String> partials = new ArrayList<String>();
		
		for (int i = 0; i < completedJobs.size(); i++) {
			if (i >= iteIndex) {
				iteJobs.add(completedJobs.get(i));

			} else {
				nonIteJobs.add(completedJobs.get(i));
				System.out.println("Target " + completedJobs.get(i).getTargetPartial());
				System.out.println(completedJobs.get(i).getCorrectMapping());
			}
		}
		
		while(!nonIteJobs.isEmpty() && partials.size() < completedJobs.size()) {
			BranchwisePredicateSynthesis job = nonIteJobs.remove(0);
			System.out.println(job.getTargetPartial());
			ArrayList<String> partialsCheck = new ArrayList<String>();
			ArrayList<String> mappingsCheck = new ArrayList<String>();
			partialsCheck.addAll(partials); partialsCheck.add(job.getTargetPartial());
			System.out.println("Checking mapping " + job.getCorrectMapping());
			mappingsCheck.add(job.getCorrectMapping()); mappingsCheck.addAll(mappings);
			String programToCheck = SMS.unifyProgramNoTransform(mappings, partialsCheck);
			boolean sound = verifier.verifyInductiveProgramSound(programToCheck, mappingsCheck);
			
			//if sound add to partials and, if partials is not completedJobs.size()-1, mappings
			if (sound) {
				partials.add(job.getTargetPartial());
				if (partials.size() < completedJobs.size()) {
					System.out.println("Adding mapping " + job.getCorrectMapping());
					mappings.add(job.getCorrectMapping());
				}
				
				System.out.println("Printing " + mappings.size());
				
			} else {
			//if unsound then move to the back
				nonIteJobs.add(job);
			}
			
		}
		
		System.out.println("Partials size " + partials.size());
		System.out.println("CompletedJobs Size " + completedJobs.size());
		
		//some lovely copy pasta, the hour grows late so whatever
		while(iteJobs.isEmpty() && partials.size() < completedJobs.size()) {
			System.out.println("In the ITE Jobs bit");
			
			System.out.println("IteJobs size is " + iteJobs.size());
			BranchwisePredicateSynthesis job = iteJobs.remove(0);
			ArrayList<String> partialsCheck = new ArrayList<String>();
			ArrayList<String> mappingsCheck = new ArrayList<String>();
			System.out.println("Target partial is " + job.getTargetPartial()); 
			partialsCheck.addAll(partials); partialsCheck.add(job.getTargetPartial());
			mappingsCheck.add(job.getCorrectMapping()); mappingsCheck.addAll(mappings);
			
			String programToCheck = SMS.unifyProgramNoTransform(mappings, partialsCheck);
			
			boolean sound = verifier.verifyInductiveProgramSound(programToCheck, mappingsCheck);
			
			//if sound add to partials and, if partials is not completedJobs.size()-1, mappings
			if (sound) {
				partials.add(job.getTargetPartial());
				if (partials.size() < completedJobs.size()) {
					mappings.add(job.getCorrectMapping());
				}
				
			} else {
			//if unsound then move to the back
				iteJobs.add(job);
			}
			
		}
		
		
		
		return SMS.detSMSbuildUnifiedProgram(mappings, partials, benchmark);
	}
	
	private static int determineITEIndex(ArrayList<BranchwisePredicateSynthesis> completedJobs) {
		int i;
		for (i = 0; i < completedJobs.size(); i++ ) {
			if (completedJobs.get(i).getTargetPartial().contains("(ite ")) {
				return i;
			}
		}
			
		return completedJobs.size();
	}
	
private static String unifyProgramNoTransform(ArrayList<String> mappings, ArrayList<String> partials) {
		
		String unifiedProgram = "";
		String closingParentheses = "";
		
		if (partials.size() == 1) {
			return partials.get(0);
		}

		System.out.println("Number of Mappings " +  mappings.size());
		System.out.println("Number of Partials " + partials.size());
		
		for (int i = 0; i < partials.size() - 1; i++) {
			System.out.println("Mappings " + (i+"") + " " + mappings.get(i));
			unifiedProgram += "(ite " + mappings.get(i) + " " + partials.get(i) + " ";
			closingParentheses += ")";
		}

		unifiedProgram += " " + partials.get(partials.size() - 1) + closingParentheses;

		return unifiedProgram;
	}
	
	/*public static void main(String[] args) {
		
	}*/
	
}

