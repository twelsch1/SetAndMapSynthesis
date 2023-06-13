package bcs.branchwisePredicateSynthesis.helpers;

import java.util.HashSet;

import bcs.utils.Utils;
import bcs.verification.Verifier;

public class ExtractPositiveMappings {

	public static HashSet<String> extractPositiveMappings(Verifier verifier, String programToModify) {
		return extractPositiveMappings(verifier, programToModify, null);
	}

	public static HashSet<String> extractPositiveMappings(Verifier verifier, String programToModify, String completeMappingWithRestrictions) {
		
//		//System.out.println("Removing cons and tauts");
		String program = programToModify;
		String[] operators = {">", "<", "<=", ">=", "=", "distinct"};
		
		HashSet<String> partialMappings = new HashSet<>();
		
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
					String predicate = program.substring(nextPredicateInstance[0], nextPredicateInstance[1]+1);
					if (verifier.isPositiveMapping(predicate, completeMappingWithRestrictions)) {
						partialMappings.add(predicate);
					}
					
					j = nextPredicateInstance[1];
					

				}

			}
			

		}
		
		////System.out.println("Escaped");
		return partialMappings;
		
	}


}
