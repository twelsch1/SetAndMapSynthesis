package evoSynthesis;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;

import bcs.benchmark.Benchmark;
import bcs.optional.Splitter;
import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
import bcs.utils.Utils;
import bcs.verification.CounterExample;
import bcs.verification.Verifier;
import ec.EvolutionState;
import ec.Evolve;
import ec.Individual;
import ec.gp.GPIndividual;
import ec.gp.GPNode;
import ec.util.Parameter;
import ec.util.ParameterDatabase;
import ecjSimple.SimpleEvolutionStateWithVerification;
import fitness.VerifiableFitness;

public class GPPartialsSynthesizer extends Synthesizer {
	
	private String paramFile;
	private Benchmark benchmark;
	private String[] runConfig;
	
	
	

	public GPPartialsSynthesizer(String paramFile, Benchmark benchmark) {
		this.paramFile = paramFile;
		this.benchmark = benchmark;
		

		String variableNamesString = String.join(",,,", benchmark.getVariableNames());
		String definedFunctionsString;
		if (benchmark.getDefinedFunctions() == null) {
			definedFunctionsString = "";
		} else {
			definedFunctionsString = String.join(",,,", benchmark.getDefinedFunctions());
		}
		
		runConfig = new String[] { Evolve.A_FILE, paramFile,
				"-p", 
				"-p", ("jobs=" + 1), "-p",
				("assertionString=" + benchmark.getAssertionString()), "-p", ("funString=" + benchmark.getFunString()),
				"-p", ("variableNamesString=" + variableNamesString), "-p", ("synthType=program"), "-p",
				("funName=" + benchmark.getFunctionName()), "-p",
				("definedFunctionsString=" + definedFunctionsString) };
	}
	
	private ParameterDatabase setupDatabase(String paramFile, String[] runConfig, Benchmark benchmark) {
		ParameterDatabase dbase = null;
		try {
			dbase = new ParameterDatabase(new File(paramFile), runConfig);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}

		String evalthreadsString = dbase.getString(new Parameter("evalthreads"), new Parameter("evalthreads"));
		int evalThreads = 1;
		if (evalthreadsString != null) {
			evalThreads = Integer.parseInt(evalthreadsString);
		}
		for (int i = 0; i < evalThreads; i++) {
			dbase.set(new Parameter("seed." + i), "time");
		}

		ParamsHelper.setFunctionSet(dbase, benchmark.getVariableNames(), benchmark.getDefinedFunctionNames());
		
		
		return dbase;
	}


	@Override
	public SynthesisResult synthesize(Verifier verifier) {
		
		boolean successful = false;
	    String bestProgram = "";
	    String split = "";
	    
	    GPNode bestProgramTree = null;
	    ArrayList<CounterExample> foundCounterExamples = null;
		
		ParameterDatabase dbase = setupDatabase(paramFile,runConfig,benchmark);
		

		//Perform evolutionary run 
		SimpleEvolutionStateWithVerification evaluatedState = (SimpleEvolutionStateWithVerification) Evolve.initialize(dbase, -1);
		evaluatedState.startFresh(verifier);


		int result = EvolutionState.R_NOTDONE;
		while( result == EvolutionState.R_NOTDONE ) {
			result = evaluatedState.evolve();
		}

		
    	ArrayList<Individual> individuals = new ArrayList<>();
	    individuals.addAll(evaluatedState.population.subpops.get(0).individuals);
	    Collections.sort(individuals);
	
	    		
	    
	    


		for (int i = 0; i < individuals.size(); i++) {
			GPIndividual ind = (GPIndividual) individuals.get(i);
			VerifiableFitness f = (VerifiableFitness) ind.fitness;
			
			if (f.isIdealFitness()) {
				String prog = ind.trees[0].child.makeLispTree();
				if (bestProgram.isEmpty() || prog.length() < bestProgram.length()) {
					bestProgram = prog;
					
				}
			}
			
			
		}
		
		
		
		if (bestProgram.isEmpty()) {
			GPIndividual ind = (GPIndividual) individuals.get(0);
			VerifiableFitness fe = (VerifiableFitness) ind.fitness;
			bestProgramTree = ind.trees[0].child;
			bestProgram = bestProgramTree.makeLispTree();	
			foundCounterExamples = fe.getFoundCounterExamples();
		
		} else {
			////System.out.println("Correct program found")
			successful = true;
		}
		
		System.out.println("Best program found: " + bestProgram);

		if (!successful) {
			if (Utils.programHasIte(bestProgram)) {
				split = Splitter.simpleSplit(bestProgram);
			}
			
			if (split == null) {
				split = "true";
			}

		}
		
		System.out.println("Split is: " + split);
		
		Evolve.cleanup(evaluatedState);
		return new SynthesisResult(successful,bestProgram,split);
	}

	


}
