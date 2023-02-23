package bcs.verification;

import java.util.ArrayList;
import java.util.Random;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Global;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;

/**
 * The Verifier class provides a verify function that will return if a program is correct or not on a given input space.
 * Variables such as localRestrictions, correctTerms, additionalTerms, globalConstraints, and repairConstraint can modify
 * this input space. These variables are set by internal functions that implement the divide and conquer algorithms. 
 * @author Thomas Welsch
 *
 */

public class Verifier {
	
	/**
	 * The name of the target function we are synthesizing e.g. max3.
	 */
	private String functionName;
	/**
	 * Temporary variable names used during synthesis.
	 */
	private String[] synthesisVariableNames;
	/**
	 * Variable names as they appear in the formal specification.
	 */
	private String[] verVarNames;
	/**
	 * Predicates that were obtained as restrictions during BPS or as Splits during Split and Conquer.
	 */
	private String[] localRestrictions;
	/**
	 * Terms (i.e. on LIA, Int programs) that during a run of Split and Conquer were perfect on a restricted input space.
	 */
	private String[] correctTerms;
	/**
	 * Terms (i.e. on LIA, Int programs) that were extracted from the best program on a restricted input space.
	 */
	private String[] additionalTerms;
	/**
	 * The partial programs for which a mapping had not yet been obtained when the synthesis job kicked off, excluding the
	 * targetPartial.
	 */
	private String[] remainingPartials;
	/**
	 * Additional functions defined in the formal specification.
	 */
	private String[] definedFunctions;
	/**
	 * Mappings obtained for partials.
	 */
	private String[] globalConstraints;
	
	/**
	 * Clauses found during RBPS.
	 */
	private String[] clauses;
	/**
	 * A predicate that is used in the repair process if initial synthesis terminates as correct
	 * but fails final verification. This can occur only when running in parallel, for more read comments in the source code in
	 * the VerificationQueries and RBPS classes.
	 */
	private String repairConstraint;
	
	/**
	 * A variable that is set to determine if an extra restriction on distinctness is enforced on positive
	 * CounterExamples. Set to true if skipToRepair is true in SynthesisParameters or if repair process is underway.
	 * False otherwise.
	 */
	private boolean omitDistinctness;
	/**
	 * The target function's declaration.
	 */
	private String functionDeclarationString;
	/**
	 * A String that is the concatenation of all the constraints from the formal specification on the target function.
	 */
	private String assertionString;
	/**
	 * The SMT Lib logic e.g. LIA obtained from the formal specification.
	 */
	private String logic; 
	/**
	 * The partial program for which predicate synthesis is attempting to synthesize a mapping such that
	 * it is true if and only if the target partial is correct on the input space restricted by globalConstraints.
	 */
	private String targetPartial;
	/**
	 * A String that can be "predicate" or "program", allows us to determine which call to make when verify is called.
	 */
	private String synthType;
	/**
	 * A string that represents a function call of the target function with variables.
	 */
	private String functionCallString;
	/**
	 * During predicate synthesis, determines the percentage of times to check for positive rather than
	 * negative counterexamples first. 
	 */
	private double pctOfPositives;
	
	/**
	 * Used for RNG.
	 */
	private Random rand;
	
	
	/**
	 * Constructor for Verifier. Does standard constructor stuff, also initializes rand, enables parallel Z3 calls globally, and builds tempVarNames.
	 * @param functionName The name of the target function we are synthesizing e.g. max3.
	 * @param verVarNames Variable names as they appear in the formal specification.
	 * @param extraAssertions Predicates that were obtained through splitting or BSPR.
	 * @param functionDeclarationString The target function's declaration.
	 * @param assertionString A String that is the concatenation of all the constraints from the formal specification on the target function.
	 * @param logic The SMT Lib logic e.g. LIA.
	 * @param correctTerms Terms (i.e. on LIA, Int programs) that during a run of Split and Conquer were perfect on a restricted input space.
	 */
	public Verifier(String functionName, String[] verVarNames, String[] extraAssertions, 
			String functionDeclarationString, String assertionString, String logic,
			 String[] correctTerms) {
		this.functionName = functionName;
		this.verVarNames = verVarNames;
		this.localRestrictions = extraAssertions;
		this.functionDeclarationString = functionDeclarationString;
		this.logic = logic;
		this.assertionString = assertionString;
		this.correctTerms = correctTerms;
		rand = new Random();
		
		//enables parallel Z3 verification globally
		Global.setParameter("parallel.enable", "true");
		
		//builds tempVarNames and functionCallString
		//synthesisVariableNames = new String[verVarNames.length];
		functionCallString = "(" + functionName;

		for (int i = 0; i < verVarNames.length; i++) {
			functionCallString += " " + verVarNames[i];
			//synthesisVariableNames[i] = "var" + (i+1) + ";";
		}
		functionCallString += ")";
		synthesisVariableNames = verVarNames;

		
	}
	
	/**
	 * Verifies if a program is correct on the input space determined by the state of the verifier.
	 * @param program The program to be verified.
	 * @param ctx The Z3 Context instance used by the Z3 SMT.
	 * @param solver Z3 solver with threads and timeout parameters set.
	 * @param counterExamples Any counterexamples found previously, optional and should only be included if program to verify is known to be incorrect.
	 * @return A model representing the input side of a CounterExample. If no model was found, returns null, indicating the program was correct.
	 * @throws VerificationException Thrown if the solver encounters an Unknown status.
	 */
	private Model verifyProgram(String program, Context ctx, Solver solver, ArrayList<CounterExample> counterExamples) throws VerificationException {
		//default return value, if still null at the end means program was correct
		Model retVal = null;
		
		/*if (variances != null && variances.size() > 1) {
			program = transformSIProgramToMI(program, variances, tempVarNames);
		}*/
		
		//generate the verification query
		String verificationString = VerificationQueries.generateProgramVerificationQuery(program, counterExamples, logic, functionName, 
				functionCallString, functionDeclarationString, assertionString, correctTerms, localRestrictions, additionalTerms, definedFunctions, 
				verVarNames, synthesisVariableNames);
		

		//System.out.println(verificationString);
		try {
			
			//run the query
			Status status = solver.check(ctx.parseSMTLIB2String(verificationString, null, null, null, null));

			//If SAT, set the retVal to be the model, if UNKNOWN throw an exception
			if (Status.SATISFIABLE == status) {
				 retVal = solver.getModel();
			} else if (Status.UNKNOWN == status) {
				throw new VerificationException(solver.getReasonUnknown() + "\n" + verificationString);
			} 
		} catch (Exception e) {
			throw e;
		} finally {
			//reset the solver for the next verification call
			solver.reset();
		}
		
		return retVal;
	}
	
	/**
	 * Verify one side of the predicate to determine if the predicate forms a partially correct mapping (i.e. correct for positive or negative counterexamples)
	 * for the input space determined from Verifier's state.
	 * @param predicate The predicate to be verified.
	 * @param ctx The Z3 Context instance used by the Z3 SMT.
	 * @param solver Z3 solvers with threads and timeout parameters set.
	 * @param direction The side of the mapping to be checked, when true we check that predicate is true for all inputs where targetPartial is correct, otherwise
	 * we check the predicate is false for all inputs where targetPartial is incorrect.
	 * @return A model representing the input side of a CounterExample. If no model was found, returns null, indicating the predicate was a correct mapping for the side that was checked.
	 * @throws VerificationException Thrown if the solver encounters an Unknown status.
	 */
	private Model verifyHalfPredicate(String predicate, Context ctx, Solver solver, boolean direction) throws VerificationException {
		String query = "";
		try {
			//Generate query
			query = VerificationQueries.generatePredicateQuery(predicate, direction, logic, functionName, repairConstraint, omitDistinctness,
					targetPartial, functionDeclarationString, assertionString, remainingPartials, localRestrictions, globalConstraints, definedFunctions, 
					verVarNames, synthesisVariableNames, clauses);
			
			//Run solver
			Status status = solver.check(ctx.parseSMTLIB2String(query, null, null, null, null));

			//if SAT return model, if UNKNOWN throw an exception
			if (Status.SATISFIABLE == status) {
				return solver.getModel();
			} else if (Status.UNKNOWN == status) {
				throw new VerificationException(solver.getReasonUnknown() + direction);
			}
			
			//System.out.println(query);

		} catch (VerificationException e) {
			//System.out.println(query);
			throw e;
		} catch (Exception e) {
			//System.out.println(query);
			throw e;
		} finally {
			//reset the solver for the next verification call
			solver.reset();
		}

		//if this has been reached there is no model for a CounterExample, so return null
		return null;

	}
	
	/**
	 * Verify if a predicate forms a full mapping to the targetPartial for the input space determined from Verifier's state.
	 * @param predicate The predicate to be verified.
	 * @param ctx The Z3 Context instance used by the Z3 SMT.
	 * @param solver Z3 solver with threads and timeout parameters set.
	 * @return A model representing the input side of a CounterExample. If no model was found, returns null, indicating the predicate was a correct mapping.
	 */
	private VerificationResult verifyPredicate(String predicate, Context ctx, Solver solver) {
		Model inputModel = null;
		
		//Generate rand in [0,1), then pick the direction to check (positive or negative) based off percentage of desired positives
		double diceRoll = rand.nextDouble();
		boolean counterexampleType = diceRoll <= pctOfPositives;
		
		try {
			//Check the side assigned based off RNG
			inputModel = verifyHalfPredicate(predicate, ctx, solver, counterexampleType);
			
			//if null, means it was correct for that side, so check the other side to see if a CounterExample exists there.
			if (inputModel == null) {
				//this line changes the side
				counterexampleType = !counterexampleType;
				inputModel = verifyHalfPredicate(predicate, ctx, solver, counterexampleType);
			}
			
			//if still null, means the predicate was correct, so we return as such
			if (inputModel == null) {
				//reset the solver for the next verification call
				return new VerificationResult(null, Status.UNSATISFIABLE);
			}
			
		} catch(Exception e ) {
			//error was encountered, set status to UKNOWN and include the exception in the result
			return new VerificationResult(Status.UNKNOWN, e);
		}
				
		//if still going, means we have a CounterExample. Get the input side from the model.
		int[] inputs = new int[verVarNames.length];
		for (int i = 0; i < verVarNames.length; i++) {
			Expr<?> expr = ctx.mkIntConst(verVarNames[i]);
			inputs[i] = Integer.parseInt(inputModel.eval(expr, true).toString());
		}
		
		//the output side is the counterexampleType that was most recently checked
		int output = counterexampleType ? 1 : 0;
		
		return new VerificationResult(new CounterExample(inputs, output), Status.SATISFIABLE);
	}
	
	/**
	 * Acquires a CounterExample by verifying again inputs on which a program previously failed. These inputs are hardcoded and a correct answer for those inputs is extracted.
	 * @param model A Z3 model that contains the input side of a CounterExample.
	 * @param ctx The Z3 Context instance used by the Z3 SMT.
	 * @param solver Z3 solver with threads and timeout parameters set.
	 * @return A full I/O CounterExample
	 * @throws VerificationException Thrown if Z3 Status from running solver was not SAT
	 */
	private CounterExample getCounterExample(Model model, Context ctx, Solver solver) throws VerificationException {
		CounterExample retVal = null;
		int[] inputs = new int[verVarNames.length];
		//get the inputs from the model
		for (int i = 0; i < verVarNames.length; i++) {
			Expr<?> expr = ctx.mkIntConst(verVarNames[i]);
			inputs[i] = Integer.parseInt(model.eval(expr, true).toString());
		}
		
		//generate the query
		String ceQuery = VerificationQueries.generateCounterexampleQuery(inputs, logic, functionDeclarationString, assertionString, 
				definedFunctions, verVarNames);
		try {
			//run the solver
			Status status = solver.check(ctx.parseSMTLIB2String(ceQuery, null, null, null, null));

			//Should return SAT, and outputForModel corresponds with the output side of the CounterExample, so that is extracted
			if (Status.SATISFIABLE == status) {
				Expr<?> expr = ctx.mkIntConst("outputForModel");
				retVal = new CounterExample(inputs, Integer.parseInt(solver.getModel().eval(expr, true).toString()));
			} else if (Status.UNKNOWN == status) {
				throw new VerificationException(solver.getReasonUnknown());
			} else {
				//Shouldn't be reached, indicates a bug earlier in the process, so throws an Exception
				throw new VerificationException("UNSAT when checking for output");
			}
		} finally {
			//reset the solver for the next verification call
			solver.reset();
		}
		
		return retVal;
	}
	
	/**
	 * Verifies if a program is correct for the input space determined by the Verifier class's state.
	 * If it is, status on the VerificationResult is set as UNSAT. If it is incorrect and a counterexample can be found, the
	 * status is set as SAT and a CounterExample on which that program is incorrect is also set. If an Exception is encountered
	 * or it is unknown if it is correct, status is set as UNKNOWN.
	 * @return VerificationResult - Contains Z3 status and, if encountered, an exception.
	 */
	public VerificationResult verify(String program) {
		//Initializes default vcp, then initializes a context via try with resources, ensuring that the context
		//is closed after try block.
		VerificationCallParameters vcp = new VerificationCallParameters();
		try (Context ctx = new Context()) {
		//Verification call is performed and VerificationResult is returned.
		return verify(program,ctx,vcp.getTimeout(),vcp.getThreads(), vcp.getCounterExamples());
		}
	}
	
	/**
	 * Verifies if a program is correct for the input space determined by the Verifier class's state.
	 * If it is, status on the VerificationResult is set as UNSAT. If it is incorrect and a counterexample can be found, the
	 * status is set as SAT and a CounterExample on which that program is incorrect is also set. If an Exception is encountered
	 * or it is unknown if it is correct, status is set as UNKNOWN.
	 * @param program The program to be verified.
	 * @param vcp A class that has optional parameters including number of threads, timeout, previously found
	 * CounterExamples and a Z3 context.
	 * @return VerificationResult - Contains Z3 status and, if encountered, an exception.
	 */
	public VerificationResult verify(String program, VerificationCallParameters vcp) {
		//If provided VerificationCallParameters does not have a context, initialize one with try with resources 
		//which ensures it closed after the try.
		if (vcp.getContext() == null) {
			try (Context ctx = new Context()) {
				//Verification call is performed and VerificationResult is returned.
				return verify(program, ctx, vcp.getTimeout(), vcp.getThreads(), vcp.getCounterExamples());
			}
		}
		//Verification call is performed using provided context and VerificationResult is returned.
		return verify(program, vcp.getContext(), vcp.getTimeout(), vcp.getThreads(), vcp.getCounterExamples());
	}
	

	/**
	 * A private function that marshals parameters from a VerificationCallParameters instance and performs
	 * the actual verification process.
	 * @param program The program to be verified.
	 * @param ctx The Z3 Context instance used by the Z3 SMT.
	 * @param timeout The time in milliseconds to allow the verification call. If -1, time is unlimited.
	 * @param threads The number of threads allocated to Z3.
	 * @param counterExamples Previously found CounterExample instances, should only be included if the program
	 * is known to be incorrect. Forces verification call to find a new CounterExample.
	 * @return VerificationResult - Contains status and, if encountered, an exception.
	 */
	private VerificationResult verify(String program, Context ctx, int timeout, int threads, ArrayList<CounterExample> counterExamples) {
		
		//initialize solver and params from the context
		Solver solver = ctx.mkSolver();
		Params params = ctx.mkParams();
		
		//if the optional parameters are included and valid, set them
		if (threads > 1) {
			params.add("threads", threads);
		}
		if (timeout > 0) {	
			params.add("timeout", timeout);
		}
		solver.setParameters(params);
		Model model = null;
		//if the synthType is program, run verifyProgram. If the model is null, return with UNSAT status indicating correctness.
		//If SAT, get the CounterExample and return.
		try {
			if (synthType.equals("program")) {

				System.out.println("Verifying program");
				model = verifyProgram(program, ctx, solver, counterExamples);
				if (model == null) {
					return new VerificationResult(null, Status.UNSATISFIABLE);
				} else {
					return new VerificationResult(getCounterExample(model, ctx, solver), Status.SATISFIABLE);
				}

			} else {
				// if synthType isn't program, run the predicate verification
				return verifyPredicate(program, ctx, solver);
			}
		} catch (Exception e) {
			return new VerificationResult(Status.UNKNOWN, e);
		}
		
		
	}
	
	/**
	 * Checks if partials cover an input space such that at least one partial in partials is correct for 
	 * any given input. If coveredAssertions is null, the input space is all inputs, otherwise it is
	 * the input space covered by coveredAssertions i.e. where each assertion in coveredAssertions is true. 
	 * @param partials A set of programs to be verified.
	 * @param coveredAssertions Predicates obtained by splitting that restrict the input space.
	 * @return True if partials are verified to cover the input space, false otherwise
	 */
	public boolean verifyPartials(String[] partials, String[] coveredAssertions) {

			//generate query
		//	String query = VerificationQueries.generatePartialsQuery(partials, coveredAssertions, logic, functionName, functionCallString,
				//	functionDeclarationString, assertionString, definedFunctions, verVarNames, tempVarNames);
		
		

			String query = VerificationQueries.generateProgramVerificationQuery
					(null, null, logic, functionName, functionCallString, functionDeclarationString,
							assertionString, partials, coveredAssertions, null, definedFunctions, verVarNames, synthesisVariableNames);
		//	System.out.println(query);

			//open context with try with resources, ensuring it will be closed after try block
			try(Context ctx = new Context()) {
				
				//Initialize solver from context
				Solver solver = ctx.mkSolver();
				//run solver and get the status
				Status status = solver.check(ctx.parseSMTLIB2String(query, null, null, null, null));

				//if UNSAT, return true
				if (status == Status.UNSATISFIABLE) {
					return true;
				} 
			} catch (Exception e) {
			//	System.out.println(e.getMessage());
				throw e;			
			} 
			
			//wasn't correct, so return false
			return false;
		}	
	
	/**
	 * A wrapper of the verify method that sets the extraAssertions and then runs a verify call and returns true
	 * if the status is UNSAT. Otherwise returns false, including if exceptions are encountered.
	 * @param program The program to be verified.
	 * @param extraAssertions Predicates that can restrict the input space.
	 * @return true if the program was verified as correct, false otherwise.
	 */
	public boolean isProgramCorrect(String program,String[] extraAssertions) {
		
		//set extraAssertions
		this.setLocalRestrictions(extraAssertions);
		return isProgramCorrect(program);
		
		
	}
	
	/**
	 * A wrapper of the verify method that sets the extraAssertions and then runs a verify call and returns true
	 * if the status is UNSAT. Otherwise returns false, including if exceptions are encountered.
	 * @param program The program to be verified.
	 * @param extraAssertions Predicates that can restrict the input space.
	 * @return true if the program was verified as correct, false otherwise.
	 */
	public boolean isProgramCorrect(String program) {

		try {
			//verify, if status is unsat return true
			VerificationResult vr = null;
			vr = this.verify(program);
			if (vr.getStatus() == Status.UNSATISFIABLE) {
				return true;
			}
		} catch(Exception e) {
			//This will cause issues for our divide and conquer methods, so we throw an exception
			System.out.println(e.toString());
			throw e;
		} 

		//if we have reached this point program was incorrect
		return false;
		
		
	}
	
	/**
	 * A wrapper of isProgramCorrect that checks is a predicate is a Complete Mapping given the extra assertions.
	 * Sets the synthType to predicate but note in the context of BranchwisePredicateSynthesis the
	 * value is already predicate anyway.
	 * @param program The program to be verified.
	 * @param extraAssertions Predicates that can restrict the input space.
	 * @return true if the program was verified as correct, false otherwise.
	 */
	public boolean isCompleteMapping(String predicate) {
		this.setSynthType("predicate");
		return isProgramCorrect(predicate);
	}
	
	public boolean isCompleteMapping(String predicate, String[] extraAssertions) {
		this.setSynthType("predicate");
		this.setLocalRestrictions(extraAssertions);
		return isProgramCorrect(predicate);
	}
	
	public boolean isPositiveMapping(String predicate, String completeMappingWithRestrictions) {

		
		String query = VerificationQueries.generatePartialMappingQuery(predicate, logic, functionName, repairConstraint, omitDistinctness,
				targetPartial, functionDeclarationString, assertionString, remainingPartials, localRestrictions, globalConstraints, definedFunctions, 
				verVarNames, synthesisVariableNames, completeMappingWithRestrictions, clauses);
		
		//System.out.println(query);
		//open context with try with resources, ensuring it will be closed after try block
		try(Context ctx = new Context()) {
			
			//Initialize solver from context
			Solver solver = ctx.mkSolver();
			//run solver and get the status
			Status status = solver.check(ctx.parseSMTLIB2String(query, null, null, null, null));

			//if UNSAT, return true
			if (status == Status.UNSATISFIABLE) {
				return true;
			} 
		} catch (Exception e) {
		//	System.out.println(e.getMessage());
			throw e;			
		} 
		
		//wasn't partial mapping or error encountered, return false
		return false;
	}
	
	/**
	 * This procedure reduces the set of partial programs (practically implemented using a list for indexing) found by removing any programs that are unnecessary to achieve unsatisfiability
	 * on the verifyPartials call.  
	 * @param partialPrograms
	 * @return An array representing the set of partials where each program is the only program that is correct for at least one input.
	 */
	public String[] reduceToNecessarySet(ArrayList<String> partialPrograms) {
		
		// The following loop eliminates any overlapping terms to prevent
		// unnecessary work. Similar operation was used in original STUN GP.
		// Basically, remove one at a time and see if the problem is still unsat and
		// thus the partials still covering. If it is unsat, add the partial to the removedPartials
		// to flag it for removal and exclude it going forward.
		ArrayList<Integer> removedPartials = new ArrayList<>();
		for (int i = 0; i < partialPrograms.size(); i++) {
			ArrayList<String> prePartials = new ArrayList<>();
			// build out the partials by index, excluding the current one and ones we have already
			// flagged for removal
			for (int j = 0; j < partialPrograms.size(); j++) {
				//
				if (i != j && !removedPartials.contains(j)) {
					prePartials.add(partialPrograms.get(j));
				}
			}

			//check if still unsat, if it is then we flag the partial for removal by adding the index 
			if (this.verifyPartials(prePartials.toArray(new String[prePartials.size()]), null)) {
					removedPartials.add(i);
			} 
			
		}
		ArrayList<String> partials = new ArrayList<String>();

		// now that we have the partials flagged by index for removal, we add only the ones
		// unflagged into final partials to be used for Predicate Synthesis.
		for (int i = 0; i < partialPrograms.size(); i++) {
			if (!removedPartials.contains(i)) {
				partials.add(partialPrograms.get(i));
			}
		}

		return partials.toArray(new String[partials.size()]);
	}
	
	
	public String getTargetPartial() {
		return targetPartial;
	}

	public void setTargetPartial(String targetPartial) {
		this.targetPartial = targetPartial;
	}

	public void setGlobalConstraints(String[] globalConstraints) {
		this.globalConstraints = globalConstraints;
	}

	public void setRemainingPartials(String[] remainingPartials) {
		this.remainingPartials = remainingPartials;
	}

	public String[] getDefinedFunctions() {
		return definedFunctions;
	}

	public void setDefinedFunctions(String[] definedFunctions) {
		this.definedFunctions = definedFunctions;
	}

	public void setAdditionalTerms(String[] additionalTerms) {
		this.additionalTerms = additionalTerms;
	}

	public String[] getLocalRestrictions() {
		return localRestrictions;
	}

	public void setLocalRestrictions(String[] localRestrictions) {
		this.localRestrictions = localRestrictions;
	}

	public void setSynthType(String synthType) {
		this.synthType = synthType;
	}

	public void setCorrectTerms(String[] correctTerms) {
		this.correctTerms = correctTerms;
	}

	public void setRepairConstraint(String repairConstraint) {
		this.repairConstraint = repairConstraint;
	}

	public void setOmitDistinctness(boolean omitDistinctness) {
		this.omitDistinctness = omitDistinctness;
	}

	public void setPctOfPositives(double pctOfPositives) {
		this.pctOfPositives = pctOfPositives;
	}

	public String getFunctionCallString() {
		return functionCallString;
	}

	public String[] getSynthesisVariableNames() {
		return synthesisVariableNames;
	}

	public void setSynthesisVariableNames(String[] synthesisVariableNames) {
		this.synthesisVariableNames = synthesisVariableNames;
	}

	public String[] getVerVarNames() {
		return verVarNames;
	}

	public void setVariances(ArrayList<ArrayList<String>> variances) {
	}
	
	
	
	public void setClauses(String[] clauses) {
		this.clauses = clauses;
	}

	public static String transformSIProgramToMI(String SIProgram, ArrayList<ArrayList<String>> variances, String[] tmpVars) {
		ArrayList<String> conditions = new ArrayList<>();
		ArrayList<String> transformedPrograms = new ArrayList<>();
		String retVal = "";
		
		for (ArrayList<String> variance : variances) {
			
			//variance size will be at least two
			if (variance.size() == 2) {
				conditions.add("(>= " + variance.get(0) + " " + variance.get(1) + ")");
			} else {
				String condition = "(and";
				for (int i = 0; i < variance.size()-1; i++) {
					condition += " (>= " + variance.get(i) + " " + variance.get(i+1) + ")";
				}
				condition += ")";
				conditions.add(condition);
			}
			
			String transformedProgram = SIProgram;
			for (int i = 0; i < variance.size(); i++) {
				
				transformedProgram = transformedProgram.replace(tmpVars[i], variance.get(i));
			}
			//System.out.println(transformedProgram);
			
			transformedPrograms.add(transformedProgram);
			
		}
		
		String closingParams = "";
		for (int i = 0; i < variances.size()-1; i++) {
			retVal += "(ite " + conditions.get(i) + " " + transformedPrograms.get(i) + " ";
			closingParams += ")";
		}
		
		retVal += transformedPrograms.get(variances.size()-1) + closingParams;
		
		return retVal;
		
	}
	
	

	
}


