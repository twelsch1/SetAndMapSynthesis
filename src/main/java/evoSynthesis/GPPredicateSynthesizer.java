package evoSynthesis;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;

import bcs.benchmark.Benchmark;
import bcs.synthesizer.SynthesisResult;
import bcs.synthesizer.Synthesizer;
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

public class GPPredicateSynthesizer extends Synthesizer {
	
	private String paramFile;
	private Benchmark benchmark;
	private String[] runConfig;
	
	
	public GPPredicateSynthesizer(String paramFile, Benchmark benchmark) {
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
				"-p", ("jobs=" + 1), "-p",
				("assertionString=" + benchmark.getAssertionString()), "-p", ("funString=" + benchmark.getFunString()),
				"-p", ("variableNamesString=" + variableNamesString), "-p", ("synthType=predicate"), "-p",
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

		boolean synthSuccessful = false;
		
		//System.out.println("Running GP");
		ParameterDatabase dbase = setupDatabase(paramFile,runConfig,benchmark);
		
		SimpleEvolutionStateWithVerification evaluatedState = (SimpleEvolutionStateWithVerification) Evolve.initialize(dbase, -1);
		
		evaluatedState.startFresh(verifier);


		int result = EvolutionState.R_NOTDONE;
		while( result == EvolutionState.R_NOTDONE ) {
			result = evaluatedState.evolve();
		}
		

		

    	ArrayList<Individual> individuals = new ArrayList<>();
	    individuals.addAll(evaluatedState.population.subpops.get(0).individuals);


	
	    String bestProgram = "";
	    GPNode bestProgramTree = null;
	    
		if (result == EvolutionState.R_SUCCESS) {
			for (int i = 0; i < individuals.size(); i++) {
				GPIndividual ind = (GPIndividual) individuals.get(i);
				VerifiableFitness f = (VerifiableFitness) ind.fitness;
				if (f.isIdealFitness()) {
					String program = ind.trees[0].child.makeLispTree();
					bestProgram = program;
					bestProgramTree = ind.trees[0].child;
					break;

				}

			}
		}
		
		
		
		
		if (bestProgram.isEmpty()) {
			
			
		    Collections.sort(individuals);
			GPIndividual ind = (GPIndividual) individuals.get(0);
			bestProgramTree = ind.trees[0].child;
			bestProgram = bestProgramTree.makeLispTree();
		
		} else {
			synthSuccessful = true;
		}
		

		Evolve.cleanup(evaluatedState);
		return new SynthesisResult(synthSuccessful,bestProgramTree.makeLispTree());
	}

}
