package bcs.verification;

import java.util.ArrayList;
/**
 * A utilities class containing static functions that generate the verification strings used in our verification calls.
 * @author Thomas Welsch
 *
 */
public class VerificationQueries {

	/**
	 * Generates a verification query that is used to verify if a program or set of programs is correct on an input space. If extraAssertions, correctTerms, and additionalTerms
	 * are null then the input space is the full input space. Otherwise, the input space is restricted such that any given input must be covered
	 * (i.e. true on each assertion) by extraAssertions. 
	 * and each partial program in additionalTerms and correctTerms must be incorrect for that input.
	 * @param program The program to be verified.
	 * @param counterExamples Any counterexamples found previously, optional and should only be included if program to verify is known to be incorrect.
	 * @param logic The SMT Lib logic e.g. LIA.
	 * @param functionName The name of the target function we are synthesizing e.g. max3.
	 * @param functionCallString A string that represents a function call of the target function with variables.
	 * @param functionDeclarationString The target function's declaration.
	 * @param assertionString A String that is the concatenation of all the constraints from the formal specification on the target function.
	 * @param correctTerms Terms (i.e. on LIA, Int programs) that during a run of Split and Conquer were perfect on a restricted input space.
	 * @param extraAssertions Predicates that were obtained through splitting that restrict the input space.
	 * @param additionalTerms Terms (i.e. on LIA, Int programs) that were extracted from the best program on a restricted input space.
	 * @param definedFunctions Additional functions defined in the formal specification.
	 * @param variableNames Variable names as they appear in the formal specification.
	 * @param tempVarNames Temporary variable names used during synthesis.
	 * @return A String containing the verification query.
	 */
	public static String generateProgramVerificationQuery(String program, ArrayList<CounterExample> counterExamples,
			String logic, String functionName, String functionCallString, String functionDeclarationString, String assertionString,
			String[] correctTerms, String[] extraAssertions, String[] additionalTerms, String[] definedFunctions,
			String[] variableNames, String[] tempVarNames) {
		String defPattern = "define-fun " + functionName;
		String parPattern = "(" + functionName;
		String retVal = "";
		
		//set the logic
		retVal += "(set-logic " + logic + ")\n";
		
		
		//Add any defined functions
		if (definedFunctions != null) {
			for (int i = 0; i < definedFunctions.length; i++) {
				retVal += definedFunctions[i] + "\n";
			}
		}
		
		//Declare variables
		for (int i = 0; i < variableNames.length; i++) {
			retVal += "(declare-fun " + variableNames[i] + " () Int)\n";
		}
		
		//If counterExamples are provided, ensure that the input is distinct from inputs given in counterexamples.
		//Ensures that a counterexample provided will be new, though correctness guarantee is lost.
		//Consequently, counterExamples should only be provided if the program to be verified is known to be incorrect
		//i.e. by evaluating first on previously found counterExamples.
		/*if (counterExamples != null) {
			retVal += "(assert (and true ";
			for (int i = 0; i < counterExamples.size(); i++) {
				CounterExample c = counterExamples.get(i);
				int[] inputs = c.getInputs();
				String equalities = "";
				if (inputs.length > 1) {
					equalities = "(not (and ";
					for (int j = 0; j < inputs.length; j++) {
						equalities += "(= " + variableNames[j] + " " + inputs[j] + ") ";
					}
					equalities += "))";
				} else {
					equalities = "(distinct " + variableNames[0] + " " + inputs[0] + ")";
				}
				
				retVal += equalities;
			}
			
			retVal += "))";
			
		}*/

		
		//Declare the target function
		String decFunString = "(declare-fun " + functionName + "(";
		for (int i = 0; i < variableNames.length; i++) {
			decFunString += "Int ";
		}
		decFunString += ") Int )\n";
		
		retVal += decFunString + "\n";
		
		//Assert that the target function is satisfiable
		retVal += "(assert " + assertionString + ")\n";
		
		//Assert that the synthesized function satisfies the negation of the requirements.
		//Any example where programString is correct will be eliminated.
		
		if (program != null) {
			retVal += functionDeclarationString.replace(defPattern, defPattern + "_synthed").replace("funToken;", program) + "\n";
			retVal += "(assert (not " +assertionString.replace(parPattern, parPattern+"_synthed") + "))\n";
			retVal += "(assert (distinct " + functionCallString + " " + program + "))\n";
		}
		
		//The below for correctTerms and additionalTerms, where present, similarly eliminates inputs on which those terms
		//are correct.

		if (correctTerms != null) {
			// for each program in correct terms, add functions String, replacing function
			// name with function name + _i where
			// i is index from 0 to n-1. Further replace funToken; with term.
			for (int i = 0; i < correctTerms.length; i++) {
				retVal += functionDeclarationString.replace(defPattern, defPattern + "_" + i).replace("funToken;",
						correctTerms[i]) + "\n";
			retVal += "(assert (distinct " + functionCallString + " " + correctTerms[i] + "))\n";
			}

			// for each program in terms, add the assertion string (assert (not ... )),
			// replacing function name
			// in assertion string with function name + _i.
			
			for (int i = 0; i < correctTerms.length; i++) {
				retVal += "(assert (not " + assertionString.replace(parPattern, parPattern + "_" + i) + "))\n";
			}
		}
		
		
		
		if (additionalTerms != null) {
			// for each program in additionalTerms terms, add functions String, replacing function
			// name with function name + _i where
			// i is index from 0 to n-1. Further replace funToken; with term.

			
			for (int i = 0; i < additionalTerms.length; i++) {
				retVal += functionDeclarationString.replace(defPattern, defPattern + "_add_" + i).replace("funToken;",
						additionalTerms[i]) + "\n";
				
				retVal += "(assert (distinct " + functionCallString + " " + additionalTerms[i] + "))\n";
				retVal += "(assert (not " + assertionString.replace(parPattern, parPattern + "_add_" + i) + "))\n";
			}
			
		}

		
		//Assert the extraAssertions, i.e. splits, ensuring that inputs can not come from outside the Conjunction of the input space they cover.
		if (extraAssertions != null) {
			for (int i = 0; i < extraAssertions.length; i++) {
				retVal += "(assert " + extraAssertions[i] + ")\n";
			}
		}
		
		//replace temporary variable names with sygus variable names	
		for (int i = 0; i < variableNames.length; i++) {
			//System.out.println(tempVarNames[i] + " " + variableNames[i]);
		 retVal = retVal.replace("var" + (i+1) + ";", variableNames[i]);
		}
		
		
		return retVal;
	}
	
	/**
	 * Generates a verification query that is used to find a matching output to inputs such that the output is a correct answer
	 * on those inputs.
	 * @param inputValues The input values obtained from a model returned by a verification call from a program that was SAT.
	 * @param logic The SMT Lib logic e.g. LIA.
	 * @param functionDeclarationString The target function's declaration.
	 * @param assertionString A String that is the concatenation of all the constraints from the formal specification on the target function.
	 * @param definedFunctions Additional functions defined in the formal specification.
	 * @param variableNames Variable names as they appear in the formal specification.
	 * @return A String containing the verification query .
	 */
	public static String generateCounterexampleQuery(int[] inputValues, String logic,
		 String functionDeclarationString, String assertionString,String[] definedFunctions, String[] variableNames) {
		String retVal = "";
		
		//sets the logic
		retVal += "(set-logic " + logic + ")\n";
		
		//declare our function that SMT will find a model for, given the input values variableValues
		retVal += "(declare-fun outputForModel () Int)\n";
		
		//replace the token with the outputForModel
		retVal += functionDeclarationString.replace("funToken;", "outputForModel") + "\n";
		
		//add in definedFunctions which may be in assertionString
		if (definedFunctions != null) {
			for (int i = 0; i < definedFunctions.length; i++) {
				retVal += definedFunctions[i] + "\n";
			}
		}
		
		//define the variables as functions with the value hardcoded from inputValues
		for (int i = 0; i < variableNames.length; i++) {
			retVal += "(define-fun " + variableNames[i] + " () Int " + inputValues[i] + ")\n";
		}
		
		//assert against the constraints on these specific inputs. Note that it isn't the negation, we want to find a model for our problem
		//that satisfies the constraints given the inputs.
		retVal += "(assert " + assertionString + ")\n";
		
			
		return retVal;
	}
	
	/**
	 * Generates a verification query that is used to determine if the set of programs in partials covers the input space
	 * such that at least one partial is correct for an input. The input space is the full input space if coveredAssertions is null, otherwise
	 * it is the inputs that are covered (i.e. true on each assertion) by coveredAssertions.
	 * @param partials The set of programs to be verified.
	 * @param coveredAssertions Predicates that were obtained through splitting that restrict the input space.
	 * @param logic The SMT Lib logic e.g. LIA.
	 * @param functionName The name of the target function we are synthesizing e.g. max3.
	 * @param functionCallString A string that represents a function call of the target function with variables.
	 * @param functionDeclarationString The target function's declaration.
	 * @param assertionString A String that is the concatenation of all the constraints from the formal specification on the target function.
	 * @param definedFunctions Additional functions defined in the formal specification.
	 * @param variableNames Variable names as they appear in the formal specification.
	 * @param tempVarNames Temporary variable names used during synthesis.
	 * @return A String containing the verification query.
	 */
	public static String generatePartialsQuery(String[] partials, String[] coveredAssertions, String logic, String functionName,
			String functionCallString, String functionDeclarationString, String assertionString,
			String[] definedFunctions, String[] variableNames, String[] tempVarNames) {
		String defPattern = "define-fun " + functionName;
		String parPattern = "(" + functionName;
		String query = "";
		
		//set the logic
		query += "(set-logic " + logic + ")\n";
		
		if (definedFunctions != null) {
			for (int i = 0; i < definedFunctions.length; i++) {
				query += definedFunctions[i] + "\n";
			}
		}
		
		
		String decFunString = "(declare-fun " + functionName + "(";
		for (int i = 0; i < variableNames.length; i++) {
			decFunString += "Int ";
		}
		decFunString += ") Int )\n";

		query += decFunString;
		//set the variables
		for (int i = 0; i < variableNames.length; i++) {
			query += "(declare-fun " + variableNames[i] + " () Int)\n";
		}
		
		//Rather than asserting the negation, we assert that there is input/output that satisfies. 
		//However, we then enforce that it be distinct from the partials we've already found.
		//Consequently, if the partials are covering this will be unsat.
		query += "(assert " +assertionString + ")\n";
		//}
		
		
		//for each program in correct terms, add functions String, replacing function name with function name + _i where
		//i is index from 0 to n-1. Further replace funToken; with term.
		for (int i = 0; i < partials.length; i++) {
			query += functionDeclarationString.replace(defPattern, defPattern + "_" + i).replace("funToken;", partials[i]) + "\n";
		}
		
		// for each program in terms, add the assertion string (assert (not ... )), replacing function name
		//in assertion string with function name + _i.
		for (int i = 0; i < partials.length; i++) {
			query += "(assert (not " + assertionString.replace(parPattern, parPattern + "_" + i) + "))\n";
		}
		
		
		// for each program in partials, we ensure any counterexamples are distinct from the output
	    // if the terms cover all possible correct outputs then the call will be unsatisfiable
		for (int i = 0; i < partials.length; i++) {
			query += "(assert (distinct " + functionCallString + " " + partials[i] + "))\n";
		}
		
		//The coveredAssertions are the extraAssertions being checked when seeing if we can skip when finding partials.
		if (coveredAssertions != null) {
			for (int i = 0; i < coveredAssertions.length; i++) {
				query += "(assert " + coveredAssertions[i] + ")\n";
			}
		}
		
		//replace temporary variable names with sygus variable names		
		for (int i = 0; i < variableNames.length; i++) {
			query = query.replace(tempVarNames[i], variableNames[i]);
		}
		
		return query;
	}
	
	/**
	 * Generates a verification query that is used to determine if the predicate forms a mapping on an input space such that it is true if and only the target partial is correct.
	 * The query actually must be called twice to check both sides of the mapping i.e. when positive is true and positive is false. The input space is the full input
	 * space if extraAssertions and globalConstraints are null. Otherwise the input space is restricted such that the inputs are covered (i.e. true on each assertion)
	 * by extraAssertions and that the inputs are false on each assertion in globalConstraints.
	 * @param predicate The predicate to be verified.
	 * @param positive The side of the mapping to be checked, when true we check that predicate is true for all inputs where targetPartial is correct, otherwise
	 * we check the predicate is false for all inputs where targetPartial is incorrect.
	 * @param logic The SMT Lib logic e.g. LIA.
	 * @param functionName The name of the target function we are synthesizing e.g. max3.
	 * @param repairConstraint A predicate that is used in the repair process if initial synthesis terminates as correct
	 * but fails final verification. This can occur only when running in parallel, for more read comments in the source code in
	 * the VerificationQueries and BSPR classes.
	 * @param omitDistinctness If set to true the requirement on distinctness for positive CounterExamples is omitted. Otherwise
	 * this requirement is enforced. True only if SynthesisParameters passed in to BSPR has skipRepair set to true 
	 * OR if repair process is occurring.
	 * @param targetPartial The partial program to which predicate maps.
	 * @param functionDeclarationString The target function's declaration.
	 * @param assertionString A String that is the concatenation of all the constraints from the formal specification on the target function.
	 * @param remainingPartials The other partial programs for which a mapping had not yet been obtained when the synthesis job kicked off.
	 * @param extraAssertions The predicates obtained through BSPR that restrict the input space.
	 * @param globalConstraints Mappings obtained for other partials, input space is restricted by forcing inputs to not come from space
	 * covered by these constraints since we already have a correct partial for them.
	 * @param definedFunctions Additional functions defined in the formal specification.
	 * @param variableNames Variable names as they appear in the formal specification.
	 * @param tempVarNames Temporary variable names used during synthesis.
	 * @return A String containing the verification query.
	 */
	public static String generatePredicateQuery(String predicate, boolean positive, String logic, String functionName,
			String repairConstraint, boolean omitDistinctness, String targetPartial, String functionDeclarationString, String assertionString,
			String[] remainingPartials, String[] extraAssertions, String[] globalConstraints, String[] definedFunctions,
			String[] variableNames, String[] tempVarNames, String[] clauses
			) {
		String defPattern = "define-fun " + functionName;
		String parPattern = "(" + functionName;
		String query = "";
		
		//set the logic
		query += "(set-logic " + logic + ")\n";
		
		//Add any defined functions
		if (definedFunctions != null) {
			for (int i = 0; i < definedFunctions.length; i++) {
				query += definedFunctions[i] + "\n";
			}
		}
		
		//Add the variables
		for (int i = 0; i < variableNames.length; i++) {
			query += "(declare-fun " + variableNames[i] + " () Int)\n";
		}
		
		//Declare the function, hardcoding it to be the program synthProgram
		query += functionDeclarationString.replace("funToken;", targetPartial) + "\n";
				
		//when positive is true, counterexamples only come if predicate is false AND program is correct.
		//This results in a positive counterexample i.e. the program is correct for this input.
		
		//otherwise, counterexamples only come when predicate is true and program is incorrect. results in a negative counterexample i.e. the program
		//is incorrect on this input.
		if (positive) {
			
			//The first line asserts inputs must come from the space where the predicate isn't true.
			//The second asserts inputs come only from the space where the synthProgram is correct.
			query += "(assert " + "(not " + predicate + "))\n";
			query += "(assert " + assertionString + ")\n";

			if (remainingPartials != null) {
				
				
				for (int i = 0; i < remainingPartials.length; i++) {
					query += functionDeclarationString.replace(defPattern, defPattern + "_remaining_" + i).replace("funToken;",
							remainingPartials[i]) + "\n";
				}

				//this makes it such that positives must come from an input where at least one 
				//other remaining term is incorrect. If any of the programs can be correct
				//on an input, there is no benefit for the mapping to be inclusive of this input.
				//This has the desirable side effect of eliminating positive counterexamples
				//where the requirements can be expressed as an implication, the premise does not hold, and consequently any program can be correct.
				
				
				if (remainingPartials.length == 1) {
					query += "(assert (not " + assertionString.replace(parPattern, parPattern + "_remaining_" + 0) + "))\n";
				} else {
					query += "(assert (not ( and  ";
					for (int i = 0; i < remainingPartials.length; i++) {
						query +=   assertionString.replace(parPattern, parPattern + "_remaining_" + i) + " ";
					}

					query += ")))\n";
				}
				
				
				//This makes it such that counterexamples can not come on inputs where the partial program is correct but 
				//another of the remaining partial
				//programs is equivalent (e.g. x and y are both 0, and thus both maxes in max(0,0,-1)).  Note that remainingPartials shrinks as
				//we find mappings, so in the case above a mapping that would achieve unsat for x could be (and (> x y) (>= x z)). This leaves the case
				//where x is equal to y, and this must be resolved in the mapping for y, which will no longer have x as a remaining term. An example
				//of such a mapping that satisfies is (and (>= y x) (>= y z)). Including this is sound serially but not sound in parallel since mappings with the same
				//remaining terms list can finish simultaneously making the tie potentially unresolvable. 
				//This is addressed with a repair process that synthesizes a solution given a repair constraint, which is a predicate that covers
				//all the inputs where the ties are not resolved. A solution synthesized with this repair constraint is then unified with the original solution
				//found on the rest of the input space. Note that omitDistinctness is set to true during the repair process, so the String generated
				//below is omitted from the query.
				if (!omitDistinctness) {
					String distinctString = "";

					distinctString += " (assert (and true ";
					for (int i = 0; i < remainingPartials.length; i++) {
						distinctString += "(distinct " + targetPartial + " " + remainingPartials[i] + ")\n ";
					}
					distinctString += "))\n";

					query += distinctString;
				}

			}
			
			
		} else {
			//The first line asserts inputs must come from the space where the predicate is true.
			//The second asserts inputs come only from the space where the synthProgram isn't correct.
			query += "(assert " + predicate + ")\n";
			query += "(assert " + "(not " + assertionString + "))\n";
		}
		
		//Assert that inputs come from the space covered by the Conjunction of extraAssertions
		if (extraAssertions != null) {
			for (int i = 0; i < extraAssertions.length; i++) {
				query += "(assert " + extraAssertions[i] + ")\n";
			}
		}
		
		//Assert that inputs cannot come from the space covered by globalConstraints i.e. inputs where we already have a correct answer.
		if (globalConstraints != null) {
			for (int i = 0; i < globalConstraints.length; i++) {
				query += "(assert (not " + globalConstraints[i] + "))\n";
			}
		}
		
		if (clauses != null) {
			for (int i = 0; i < clauses.length; i++) {
				query += "(assert (not " + clauses[i] + "))\n";
			}
		}
		
		//Assert that inputs come from the space covered by the repairConstraint i.e. in the repair process, the inputs where the ties were not necessarily resolved
		//from initial run.
		if (repairConstraint != null && !repairConstraint.isBlank()) {
			query += "(assert " + repairConstraint + ")";
		}
		
		//replace temporary variable names with sygus variable names	
		for (int i = 0; i < variableNames.length; i++) {
			//System.out.println(tempVarNames[i] + " " + variableNames[i]);
			query = query.replace("var" + (i+1) + ";", variableNames[i]);
		}
		
		//System.out.println(query);
		
		return query;
	}

	public static String generatePartialMappingQuery(String predicate, String logic, String functionName,
			String repairConstraint, boolean omitDistinctness, String targetPartial, String functionDeclarationString,
			String assertionString, String[] remainingPartials, String[] extraAssertions, String[] globalConstraints,
			String[] definedFunctions, String[] variableNames, String[] tempVarNames, String completeMappingWithRestrictions, 
			String[] clauses) {
		String defPattern = "define-fun " + functionName;
		String parPattern = "(" + functionName;
		String query = "";

		// set the logic
		query += "(set-logic " + logic + ")\n";

		// Add any defined functions
		if (definedFunctions != null) {
			for (int i = 0; i < definedFunctions.length; i++) {
				query += definedFunctions[i] + "\n";
			}
		}

		// Add the variables
		for (int i = 0; i < variableNames.length; i++) {
			query += "(declare-fun " + variableNames[i] + " () Int)\n";
		}
		
		query += functionDeclarationString.replace("funToken;", targetPartial) + "\n";

		if (remainingPartials != null) {

			for (int i = 0; i < remainingPartials.length; i++) {
				query += functionDeclarationString.replace(defPattern, defPattern + "_remaining_" + i)
						.replace("funToken;", remainingPartials[i]) + "\n";
			}

			// this makes it such that positives must come from an input where at least one
			// other remaining term is incorrect. If any of the programs can be correct
			// on an input, there is no benefit for the mapping to be inclusive of this
			// input.
			// This has the desirable side effect of eliminating positive counterexamples
			// where the requirements can be expressed as an implication, the premise does
			// not hold, and consequently any program can be correct.

			if (remainingPartials.length == 1) {
				query += "(assert (not " + assertionString.replace(parPattern, parPattern + "_remaining_" + 0) + "))\n";
			} else {
				query += "(assert (not ( and  ";
				for (int i = 0; i < remainingPartials.length; i++) {
					query += assertionString.replace(parPattern, parPattern + "_remaining_" + i) + " ";
				}

				query += ")))\n";
			}

			// This makes it such that counterexamples can not come on inputs where the
			// partial program is correct but
			// another of the remaining partial
			// programs is equivalent (e.g. x and y are both 0, and thus both maxes in
			// max(0,0,-1)). Note that remainingPartials shrinks as
			// we find mappings, so in the case above a mapping that would achieve unsat for
			// x could be (and (> x y) (>= x z)). This leaves the case
			// where x is equal to y, and this must be resolved in the mapping for y, which
			// will no longer have x as a remaining term. An example
			// of such a mapping that satisfies is (and (>= y x) (>= y z)). Including this
			// is sound serially but not sound in parallel since mappings with the same
			// remaining terms list can finish simultaneously making the tie potentially
			// unresolvable.
			// This is addressed with a repair process that synthesizes a solution given a
			// repair constraint, which is a predicate that covers
			// all the inputs where the ties are not resolved. A solution synthesized with
			// this repair constraint is then unified with the original solution
			// found on the rest of the input space. Note that omitDistinctness is set to
			// true during the repair process, so the String generated
			// below is omitted from the query.
			if (!omitDistinctness) {
				String distinctString = "";

				distinctString += " (assert (and true ";
				for (int i = 0; i < remainingPartials.length; i++) {
					distinctString += "(distinct " + targetPartial + " " + remainingPartials[i] + ")\n ";
				}
				distinctString += "))\n";

				query += distinctString;
			}

		}
		
		if (completeMappingWithRestrictions != null) {
			query += "(assert " + completeMappingWithRestrictions + ")\n";
		}
		
		query += "(assert (not (=> " + assertionString + " " + predicate + ")))\n";

		/*if (extraAssertions != null) {
			for (int i = 0; i < extraAssertions.length; i++) {
				query += "(assert " + extraAssertions[i] + ")\n";
			}
		}*/

		// Assert that inputs cannot come from the space covered by globalConstraints
		// i.e. inputs where we already have a correct answer.
		if (globalConstraints != null) {
			for (int i = 0; i < globalConstraints.length; i++) {
				query += "(assert (not " + globalConstraints[i] + "))\n";
			}
		}
		
		if (clauses != null) {
			for (int i = 0; i < clauses.length; i++) {
				query += "(assert (not " + clauses[i] + "))\n";
			}
		}
		

		// Assert that inputs come from the space covered by the repairConstraint i.e.
		// in the repair process, the inputs where the ties were not necessarily
		// resolved
		// from initial run.
		if (repairConstraint != null && !repairConstraint.isBlank()) {
			query += "(assert " + repairConstraint + ")";
		}

		// replace temporary variable names with sygus variable names
		for (int i = 0; i < variableNames.length; i++) {
			query = query.replace(tempVarNames[i], variableNames[i]);
		}

		return query;
	}
	

}
