package sms.branchwisePredicateSynthesis.helpers;

import sms.utils.Utils;
import sms.verification.Verifier;

public class Reduction {
	
	/**
	 * Goes through a program and iteratively checks all of its boolean operator functions. If these functions can be replaced by false or
	 * true without changing correctness, this change is made. Note that this function requires up to 2 verifications calls for every
	 * occurrence of a boolean operator so it can take multiple seconds to terminate if the program in question is long.<br><br>
	 *  
	 * This function is called and is needed within the context of RBPS. Consider that
	 * while individual boolean variables may be meaningless contradictions/tautologies when a program is initially deemed unsat, this could be
	 * because of restrictions from extraAssertions that will be relaxed during BSPR process. As an example, 
	 * consider we are synthesizing a mapping for x in <strong>max(x,y,z)</strong>.
	 * Let an extraAssertion on the input space be <strong>(and (>= x 7) (>= x y))</strong> i.e. x must be gte 7 and y for any CounterExample.
	 * Under this input space, we find the following mapping to x, <strong>(and (>= x z) (>= x 3))</strong>. This is a correct mapping on this input
	 * space, as we now have covered the scenario where x is greater than y and z. Further, x must be gte 7, so x gte 3 is a tautology. However,
	 * in the relaxation process we now remove the extraAssertion and try and synthesize a solution for the space with the new restriction of
	 * <strong>(and (>= x z) (>= x 3))</strong>. A correct solution here could be <strong>(>= x y)</strong>. This would then conclude the BSPR process,
	 * and the full mapping for x would be <strong>(and (and (>= x z) (>= x 3)) (>= x y))</strong>. But for this mapping there exists a CounterExample where x is less
	 * than 3 but x is still greater than z and y, so this is not a correct mapping. This function is called, to avoid this issue. Moving back
	 * to the original success of <strong>(and (>= x z) (>= x 3))</strong>, we would run this function and modify it to be
	 * <strong>(and (>= x z) true)</strong>. We then have this as a restriction and synthesize <strong>(>= x y)</strong> concluding BSPR, but 
	 * this time the full mapping for x is <strong>(and (and (>= x z) true) (>= x y))</strong> which is a correct mapping.

	 * @param verifier A Verifier class instance used for verification, synthProgram has been set by BSPR, globalConstraints
	 * and repairConstraint may be set by BSPR, the extraAssertions are set explictly with the extraAssertions below
	 * @param predicateToReduce The program we are seeking to reduce to a Clausal Positive Mapping.
	 * @param extraAssertions The extraAssertions that have been obtained up to this point in the BSPR process.
	 * @return The program modified such that any contradictions and tautologies on the input space covered by verifier are respectively
	 * transformed into false/true.
	 */
	public static String reduceToClausalPositiveMapping(Verifier verifier, String predicateToReduce, String[] extraAssertions) {
		
//		////System.out.println("Removing cons and tauts");
		String program = predicateToReduce;
		String[] operators = {">", "<", "<=", ">=", "=", "distinct"};
		
		//we check every comparison operator. If there were boolean variables we'd need to check those as well, but currently no CLIA problems
		//in Sygus have these.
		for (int i = 0; i < operators.length; i++) {

			//j is the index we use to track where we are in the program String, starts at 0 to initially include whole String
			int j = 0;
			while (true) {
				//looks for the next instance of the operator, if one exists gives the start and end indices so we can replace,
				//if it is does not exist returns null and we break this inner loop 
				int[] nextPredicateInstance = Utils.findNextPredicateInstance(program, operators[i],
						j);

				if (nextPredicateInstance == null) {
					//operator wasn't found, so break this inner loop and move to the next operator
					break;
				} else {
					
					//Using the nextPredicateInstance array, we get the substrings from the full program that are immediately before the
					//operator function and immediately after.
					String prePred = program.substring(0, nextPredicateInstance[0]);
					String postPred = program.substring(nextPredicateInstance[1] + 1);
					
					//Substitute in false and true to see if these are contradictions or tautologies. If they are, modify the
					//program String to just be false/true respectively where the operator used to be, and then calculate the new
					//position for j
					if (verifier.isProgramCorrect(prePred + " false " + postPred, extraAssertions)) {
						j = (prePred + " false ").length() - 1;
						program = prePred + " false " + postPred;
					} else if (verifier.isProgramCorrect(prePred + " true " + postPred, extraAssertions)) {
						j = (prePred + " true ").length() - 1;
						program = prePred + " true " + postPred;
					} else {
						//If we've gotten here we didn't need to modify, set J to just the endIndex from the parentheses so this
						//instance of the operator is skipped over on next call of findNextPredicateInstance.
						j = nextPredicateInstance[1];
					}

				}

			}
			

		}
		
		//////System.out.println("Escaped");
		return program;
		
	}

}
