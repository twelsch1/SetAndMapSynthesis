package evoSynthesis;


import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import com.microsoft.z3.Status;

import bcs.optional.CounterExamplesManager;
import bcs.optional.VerificationCallable;
import bcs.verification.CounterExample;
import bcs.verification.VerificationCallParameters;
import bcs.verification.VerificationException;
import bcs.verification.VerificationResult;
import bcs.verification.Verifier;
import datatypes.IntData;
import ec.EvolutionState;
import ec.Fitness;
import ec.Individual;
import ec.gp.GPIndividual;
import ec.gp.GPProblem;
import ec.simple.SimpleFitness;
import ec.simple.SimpleProblemForm;
import ec.util.Parameter;
import ecjSimple.SimpleEvolutionStateWithVerification;
import fitness.VerifiableFitness;


@SuppressWarnings("serial")
public class CLIAProblem extends GPProblem implements SimpleProblemForm  {

	public static final String P_DATA = "data";
	private String synthType;

	private boolean regression = true;
	private boolean doVerification = true;
	
	//public static String[] variableNames;
	//used by ecjvar's to know what to substitute in on eval...
	public int currentInputs[];
	//maximum number of tests allowed, helps us to avoid things getting out of control 
	private int maxTests = 250;
	private boolean allowDuplicates = false;
	private int initialTests = 50;
	
	private int verificationNumThreads = 1;
	
	private HashSet<String> encounteredPrograms = new HashSet<>();
	
	private int maxAttemptsFactor = 1;
	private int maxCalls = 5;
	
	//maximum number of tests allowed per generation
	private int maxTestsPerGeneration = 10;
	
	//runs a full verification every verificationFrequency generations
	private int verificationFrequency = 2; 

	
	private int incorrectVerificationTimeout = 200;
	
	
	private Verifier verifier;
	
	CounterExamplesManager ceManager = null;
			
	
	
    public void setup(final EvolutionState state,
                      final Parameter base) {

        super.setup(state,base);
        SimpleEvolutionStateWithVerification st = (SimpleEvolutionStateWithVerification) state;
        if (st.getVerifier() != null) {
        	verifier = st.getVerifier();
        }

		synthType = state.parameters.getString(new Parameter("synthType"), new Parameter("synthType"));
		


		doVerification = state.parameters.getBoolean(new Parameter("doVerification"), new Parameter("doVerification"), true);

		verificationNumThreads = state.parameters.getInt(new Parameter("verificationthreads"), new Parameter("verificationthreads"), 1);
		
		
		ceManager = new CounterExamplesManager(allowDuplicates,maxTests,synthType);
        
    }
    
    public void evaluate(final EvolutionState state, 
            final Individual ind, 
            final int subpopulation,
            final int threadnum) {
		if (!ind.evaluated) {  // don't bother reevaluating if evaluated on a previous generation, wasn't perfect anyway and would add overhead.
			

		   IntData input = new IntData();
		   int hits = 0;
		   float sum = 0;
		   float positiveSum = 0;
		   float negativeSum = 0;
		   float result;
		   
		   final ArrayList<Fitness> trials = new ArrayList<Fitness>();
		   ArrayList<CounterExample> counterExamples = ceManager.retrieveActiveCounterExamples();
		   for (int i = 0; i < counterExamples.size(); i++) {
			   CounterExample ce = counterExamples.get(i);
			   currentInputs = ce.getInputs();
		       int expectedResult = ce.getOutput();
		       ((GPIndividual)ind).trees[0].child.eval(
			           null,0,input,null,null,this);
		       int hit = expectedResult == input.x ? 1 : 0;
		       if (regression && synthType.equals("program")) {
		    	   result = Math.abs(expectedResult - input.x);
				} else {
					result = Math.abs(hit - 1);
				}
               final SimpleFitness trialFitness = new SimpleFitness();
               trialFitness.setFitness(state, hit, false);
               trials.add(trialFitness);
		       hits += hit;
		       sum += result;
	    	   if (synthType.equals("predicate") && expectedResult == 1) {
	    		   positiveSum += result;
	    	   } else if (synthType.equals("predicate") && expectedResult == 0) {
	    		   negativeSum += result;
	    	   }
		   }
		   
		   VerifiableFitness f = ((VerifiableFitness)ind.fitness);
		   f.trials = trials;
		      
		   int numNegatives = ceManager.countNegatives();
		   int numPositives = ceManager.countPositives();
		   
		   if (synthType.equals("predicate") && numPositives > 0 && numNegatives > 0) {

			   //if perfect, (numPositives - positiveSum)/numPositives = 1, so we subtract that from 1
			   //as 0 means ideal while higher means worse for standardizedFitness.
			   
			   //we take the fitness as the higher of the two sums i.e. the worse performing
			   positiveSum = 1-  ((numPositives - positiveSum) / numPositives);
			   negativeSum = 1 - ((numNegatives - negativeSum) / numNegatives);
			   f.setPositiveSum(positiveSum);
			   f.setNegativeSum(negativeSum);
			   sum = positiveSum > negativeSum ? positiveSum : negativeSum;
		   }
		   
		   f.setStandardizedFitness(state, sum);
		   f.hits = hits;
		   ind.evaluated = true;
	
		}
		
		if(Thread.interrupted()) {
			SimpleEvolutionStateWithVerification st = (SimpleEvolutionStateWithVerification) state;
			st.setInterrupted(true);
		 }
	}
  
    public void verifyPopulation(ArrayList<Individual> individuals, boolean add, int maxTestsAllowed,
			int threads) throws InterruptedException  {
    	
    	if (threads == 1 ) {
    		verifyPopulationSerial(individuals, add, maxTestsAllowed);
    	} else {
    		verifyPopulationParallelStreaming(individuals, add, maxTestsAllowed, threads);
    	}
    	
    }
    
    public boolean verifyPerfectIndividuals(ArrayList<Individual> individuals, int maxCalls) {
    	
    	int i = 0;
    	int callsMade = 0;
    	while (i < individuals.size() && callsMade < maxCalls) {
    		
    		Individual ind = individuals.get(i);
    		String program = ((GPIndividual) ind).trees[0].child.makeLispTree();
    		VerifiableFitness f = (VerifiableFitness) individuals.get(i).fitness;

  
    		if (f.hits == ceManager.countCounterExamples()) {
				try {
					callsMade++;
					VerificationResult vr = verifier.verify(program);
					if (vr.getStatus() == Status.UNSATISFIABLE) {
						////System.out.println("Found perfect program");
						f.setVerified(true);
						return true;
					} else if (vr.getStatus() == Status.SATISFIABLE) {
						f.setCounterExample(vr.getCounterExample());
					} else {
						throw vr.getException();
					}
				} catch (VerificationException e) {
					////System.out.println(e.toString());
				} catch (Exception e) {
					////System.out.println(e.toString());
				}
    		}
    		i++;
    		
    	}
    	return false;
    }
    
	@SuppressWarnings("unchecked")
	public void verifyPopulationParallelStreaming(ArrayList<Individual> individuals, boolean add, int maxTestsAllowed,
			int threads) throws InterruptedException {

		Collections.sort(individuals);

		int i = 0;
		int numCounterExamplesFound = 0;
		int activeThreads = 0;
		int attempts = 0;
		 
		ArrayList<CounterExample> initialCounterExamples = ceManager.retrieveActiveCounterExamples();

		int maxAttempts = maxTestsAllowed * maxAttemptsFactor;
		// get counterexamples from the programs that have already been verified and are
		// perfect.
		// breaks loop once a non-perfect program found
    	while (i < individuals.size()) {
    		VerifiableFitness f = (VerifiableFitness) individuals.get(i).fitness;
    		CounterExample ce = f.getCounterExample();
    		i++;
    		if (ce == null) {
    			break;
    		}
    		numCounterExamplesFound += ceManager.appendToCounterExamples(ce) ? 1 : 0;
    		
    	}

		ExecutorService exec = Executors.newFixedThreadPool(threads);
		CompletionService<VerificationResult> ecs = new ExecutorCompletionService<VerificationResult>(exec);

		try {

			// if add is true, then we go until we have generated the max tests allowed per
			// generation or hit our maximum attempts
			while (add && i < individuals.size() && attempts < maxAttempts && numCounterExamplesFound < maxTestsAllowed) {
				////System.out.println("hi");
				if (activeThreads == threads) {
					VerificationResult vr = null;
					try {
						vr = ecs.take().get();
						
						if (vr.getStatus() == Status.SATISFIABLE) {
							numCounterExamplesFound += ceManager.appendToCounterExamples(vr.getCounterExample()) ? 1 : 0;

						} else if (vr.getStatus() == Status.UNKNOWN && vr.getException() != null) {
							//vr.getException().printStackTrace();
							////System.out.println(vr.getException().getMessage());
						}
						
					} catch (InterruptedException e) {
						throw e;
					} catch (ExecutionException e) {
						e.printStackTrace();
						//System.out.println(e.getMessage());
					}
					

					
					activeThreads--;

				} else {

					String program = ((GPIndividual) individuals.get(i)).trees[0].child.makeLispTree();
					if (!encounteredPrograms.contains(program)) {
						if (Thread.interrupted()) {
							throw new InterruptedException("Interrupted");
						}
						ecs.submit(new VerificationCallable(program, verifier, initialCounterExamples,incorrectVerificationTimeout));
						encounteredPrograms.add(program);
						attempts++;
						activeThreads++;
					}

					i++;

				}
			}

		} finally {
			exec.shutdownNow();
		}

	}
    
    @SuppressWarnings("unchecked")
	public void verifyPopulationSerial(ArrayList<Individual> individuals, boolean add, int maxTestsAllowed) {
    	Collections.sort(individuals);
    	int i = 0;
    	int numCounterExamplesFound = 0;
    	
    	
    	
    	int maxAttempts = maxTestsAllowed*maxAttemptsFactor;
    	//get counterexamples from the programs that have already been verified, we always do this
    	//why did we comment this out?
    	while (i < individuals.size()) {
    		VerifiableFitness f = (VerifiableFitness) individuals.get(i).fitness;
    		CounterExample ce = f.getCounterExample();
    		i++;
    		if (ce == null) {
    			break;
    		}
    		numCounterExamplesFound += ceManager.appendToCounterExamples(ce) ? 1 : 0;
    		
    	}
    	    	
    	//if add is true, then we go until we have verified all programs or generated the max tests allowed per generation.
    	while (add && i < individuals.size() && i < maxAttempts && numCounterExamplesFound < maxTestsAllowed) {
    		String program = ((GPIndividual)individuals.get(i)).trees[0].child.makeLispTree();
    		if (!encounteredPrograms.contains(program)) {
    			encounteredPrograms.add(program);
    		} else {
    			i++;
    			continue;
    		}
    	
 
    		try {
    			VerificationCallParameters vcp = new VerificationCallParameters(ceManager.retrieveActiveCounterExamples(),2000,verificationNumThreads,null);
    			VerificationResult vr = verifier.verify(program, vcp);
    			if (vr.getStatus() == Status.UNKNOWN && vr.getException() != null) {
    				throw vr.getException();
    			}
    			
    			
				if (vr.getStatus() == Status.SATISFIABLE) {
	    			numCounterExamplesFound += ceManager.appendToCounterExamples(vr.getCounterExample()) ? 1 : 0;
	    		} 
			} catch (VerificationException e) {
				////System.out.println(e.toString());
			} catch (Exception e) {
				////System.out.println(e.toString());
			}
    		
    		
    		  
    		i++;
    	}	
    }
    
    
    public void preEvaluation(final EvolutionState state, final int threadnum) {
    	

		if (doVerification) {
			if (state.generation == 0) {
				////System.out.println("Kick off for new GP process, let's get some CounterExamples");
				ArrayList<Individual> individuals = new ArrayList<>();
				individuals.addAll(state.population.subpops.get(0).individuals);
				try {
					verifyPopulation(individuals, true, initialTests,verificationNumThreads);
				} catch (InterruptedException e) {
					//System.out.println("Apparently here");
					SimpleEvolutionStateWithVerification st = (SimpleEvolutionStateWithVerification) state;
					st.setInterrupted(true);
				}
			}
		}
	
    }
    

	public void postEvaluation(final EvolutionState state, final int threadnum)  {


    	if (doVerification) {
    		boolean perfectFound = verifyPerfectIndividuals(state.population.subpops.get(0).individuals, maxCalls);
    		ArrayList<Individual> individuals = state.population.subpops.get(0).individuals;
			if (state.generation == state.numGenerations - 1) {

				if (!perfectFound) {
					
					for (int i = 0; i < individuals.size(); i++) {
						((VerifiableFitness) ((GPIndividual) individuals
								.get(i)).fitness).setFoundCounterExamples(ceManager.retrieveActiveAndDiscardedCounterExamples());
					}

				}

			} else if (state.generation > 0) {
							
				if (!perfectFound) {
					try {
						verifyPopulation(individuals, state.generation % verificationFrequency == 0, maxTestsPerGeneration,
								verificationNumThreads);
					} catch (InterruptedException e) {
						////System.out.println("Got here");
						SimpleEvolutionStateWithVerification st = (SimpleEvolutionStateWithVerification) state;
						st.setInterrupted(true);
					}

					for (Individual individual : individuals) {
						individual.evaluated = false;
					}
				}

			}

			/*if (synthType.equals("predicate")) {
				//System.out.println("Positive Tests: " + ceManager.countPositives());
				//System.out.println("Negative Tests: " + ceManager.countNegatives());
			} else {
				//System.out.println("Total Tests: " + ceManager.countCounterExamples());
			}*/
		}

		if (Thread.interrupted()) {
			SimpleEvolutionStateWithVerification st = (SimpleEvolutionStateWithVerification) state;
			st.setInterrupted(true);
		}
    	
	}

    
}
