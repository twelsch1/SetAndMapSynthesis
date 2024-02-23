package sms.utils;

import java.util.ArrayList;
import java.util.HashSet;

import sms.benchmark.Benchmark;
import sms.verification.Verifier;

/**
 * A utilities class containing string manipulation, modification and extraction methods.
 * @author Thomas Welsch
 *
 */
public class Utils {
	



public static HashSet<String> extractPositiveMappings(Verifier verifier, String programToModify) {
	return extractPositiveMappings(verifier, programToModify, null);
}

public static HashSet<String> extractPositiveMappings(Verifier verifier, String programToModify, String completeMappingWithRestrictions) {
	
//	////System.out.println("Removing cons and tauts");
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
	
	//////System.out.println("Escaped");
	return partialMappings;
	
}


/**
 * Takes the fullProgram String and substrings it from startIndex, then checks this substring to see if the 
 * targetOperator is present. If it is, we determine where the boolean operator begins as a function to where it ends
 * i.e. the opening and closing parentheses. 
 * @param fullProgram The program to check for next predicate instance
 * @param targetOperator The boolean operator (e.g. =>, <) we are searching for
 * @param startIndex The index in fullProgram from which to start the search
 * @return If the targetOperator is found, an int array containing the indices of the opening and closing brackets of this operator. If it not
 * found returns null.
 */
public static int[] findNextPredicateInstance(String fullProgram, String targetOperator, int startIndex) {
		
		//The rest of the program after the startIndex
		String remainingProgram = fullProgram.substring(startIndex);
		
		//searches for the targetOperator, returns the index of the first instance it is found
		int targetIndex = remainingProgram.indexOf(targetOperator);
		

		//if the targetOperator isn't found, return null. This is used as a signal to
		//tell that we no longer need to check for this operator
		if (targetIndex == -1) {
			return null;
		}
		
		
		
		//use this to find the enclosing parentheses e.g. goes from >= back to (>= or ( >=, etc.
		for (int i = targetIndex; i >= 0; i-- ) {
			if (remainingProgram.charAt(i) == '(') {
				targetIndex = i;
				break;
			}
		}
		
		
		int enclosingIndex = -1;
		int parenCounter = 0;
		//The parenCounter ensures that we don't quit until we reach the closing bracket that matches the initial opening bracket
		//at the targetIndex.
		for (int i = targetIndex; i < remainingProgram.length(); i++) {
			if (remainingProgram.charAt(i) == '(') {
				parenCounter++;
			} else if (remainingProgram.charAt(i) == ')') {
				parenCounter--;
			}
			
			//when encountered, set the enclosingIndex and end the loop.
			if (parenCounter == 0) {
				enclosingIndex = i;
				i = remainingProgram.length();
			}
			
		}
		
		
		//return the indices in fullProgram where function begins and ends
		int[] retVal = new int[2];
		retVal[0] = startIndex+targetIndex;
		retVal[1] = startIndex+enclosingIndex;
		
		return retVal;
	}

/**
 * Extracts the possible terms from a given program by resolving the possible outcomes of ite branches. As an example, from the
 * LIA program <strong>(ite (>= x y) (ite (>= y z) y z) x)</strong> we would return the list <strong>[y,z,x]</strong>. 
 * Note that this operation can grow at a 2^n rate as nested ite's are resolved. Consequently it is capped by a user 
 * chosen maxExpansions to ensure timely termination.
 * @param rootProgramString The program from which terms are extracted.
 * @param maxExpansions The maximum amount of expansions we allow before terminating the function.
 * @return If maxExpansions is not passed, returns a list of terms representing all possible resolutions of 
 * the program. Otherwise, returns null.
 */
public static ArrayList<String> extractTerms(String rootProgramString, int maxExpansions) {
	
		
   ArrayList<String> extractedTerms = new ArrayList<>();
   ArrayList<String> needExtraction = new ArrayList<>();
   
   //add the program to needExtraction
   needExtraction.add(rootProgramString);
   
   //while terms still need to be extracted and we haven't gone over maxExpansions, keep extracting
   while (!needExtraction.isEmpty() && needExtraction.size()+extractedTerms.size() < maxExpansions) {
	   //take the first element from needExtraction
	   String programString = needExtraction.remove(0);
	   
	   //if it is an ite, find the index and then extract the possible terms from it
	   if (Utils.programHasIte(programString)) {

		   //finds the first ITE instance
			int idx = findNextITEIndex(programString);
			
			//extracts that ITE and then its two possible outcomes
			String[] extractedStrings = Utils.extractNextITETerms(programString, idx);
			//add these two possible outcomes to needExtraction as they could also contain ite's.
			needExtraction.add(extractedStrings[0]);
			needExtraction.add(extractedStrings[1]);
	   } else {
		   //if it isn't an ite, add to extracted terms
		   extractedTerms.add(programString);
	   }
   }
		

   //if we went over maxExpansions, return null
	if (needExtraction.size() +
			extractedTerms.size() >= maxExpansions) {
		return null;
	}
	
	

	return extractedTerms;
}

/**
 * Checks if a program is an ite function.
 * @param program The program to be checked
 * @return True if the root operator of the program is ite, false otherwise.
 */
public static boolean isITE(String program) {
	if (program.length() < 5)
		return false;
	
	return program.subSequence(0, 5).equals("(ite ");
}

/**
 * Checks if a program contains an ite function.
 * @param program The program to be checked.
 * @return True if the program contains an ite, false otherwise.
 */
public static boolean programHasIte(String program) {
	return program.contains("(ite ");
}

/**
 * Extracts the next ite function and splits it into three parts: the predicate and the two possible outcomes. Note that this
 * function assumes a program contains an ite. Consequently, <strong>programHasIte(program)</strong> should be called to 
 * confirm this beforehand.
 * @param program The program to be checked.
 * @param startIndex The index in the program from which to start checking.
 * @return The predicate and two possible outcomes from the next ite in a String array.
 */
public static String[] extractNextITEParts(String program, int startIndex) {
	String[] parts = new String[3];
	
	int i = startIndex;
	//extract the next ite from program starting from startIndex
	String iteString = extractNextFunction(program.substring(i));
	
	//by setting to 5, we skip over "(ite " to get to the predicate
	i = 5;
	
	//extracts the predicate
	parts[0] = extractNextFunction(iteString.substring(i));

	//move i up by the predicate's length plus 1 (skips the space) to move onto the first possible outcome
	i += parts[0].length()+1;

	//extract first possible outcome
	parts[1] = extractNextFunction(iteString.substring(i));	
	
	//move i up by the first possible outcome's length plus 1 to move onto the second possible outcome.
	i += parts[1].length()+1;

	//extract the second possible outcome
	parts[2] = extractNextFunction(iteString.substring(i));
	
	
	
	return parts;
}

/**
 * Extracts the two possible outcomes from the next ite function in program. Note that this
 * function assumes a program contains an ite and that startIndex is where this ite function begins.
 * The startIndex should be found using <strong> findNextITEIndex(program)</strong> beforehand.
 * @param program The program to extract from.
 * @param startIndex The index from which to start the extraction.
 * @return
 */
private static String[] extractNextITETerms(String program, int startIndex) {
		
	String[] extractedStrings = new String[2];
	//Gets the three parts of the ite: predicate and two possible outcomes
	String[] parts = extractNextITEParts(program, startIndex);
	
	//the length of the ite is calculated from the length of the parts + the length of "(ite " + the two spaces between
	//predicate and possible outcomes + the closing bracket.
	int iteLength = 8 + parts[0].length() + parts[1].length() + parts[2].length();
	
	//for the extracted strings, we remove the original ite and create two new strings where the possible outcomes
	//are inserted in their place.
	extractedStrings[0] = program.substring(0, startIndex) + parts[1] + program.substring(startIndex+iteLength);
	extractedStrings[1] = program.substring(0, startIndex) + parts[2] + program.substring(startIndex+iteLength);	
	
	return extractedStrings;
	}
	


/**
 * Extracts the first function OR constant/variable from the programSubstring. 
 * @param programSubstring The substring of a program that we are checking.
 * @return If the programSubstring starts with an open bracket, will return the remaining string up to and inclusive of the matching
 * closing bracket. If it does not start with an open bracket, it will build out the string until white space is encountered.
 */
public static String extractNextFunction(String programSubstring) {
	//if program is not well formed this function can get stuck in an infinite loop, so be careful
	
	
	//If the first character is not an open bracket, go until we find a space.
	//This can be encountered for constants and variables.
	if (programSubstring.charAt(0) != '(') {
		int x = 0;
		StringBuilder buffer = new StringBuilder("");
		//build out string until space is encountered or we have reached closing bracket of enclosing function
		// e.g. on (ite (>= x y) x y) this would be encountered on the closing bracket after y. 
		//We don't want to include either of these, so we break and return what we've got.
		//The final stopping condition is for if the whole string is itself a constant/variable. 
		//Not encountered in the way our internal functions currently
		//use this function i.e. in the context of ite's, but plausibly could be if used in other circumstances.

		while (x < programSubstring.length() && programSubstring.charAt(x) != ' ' && programSubstring.charAt(x) != ')') {


			//append most recent character and move index up 1
			buffer.append(programSubstring.charAt(x));
			x++;

		}
		//return the built out string
		return buffer.toString();
	}
	
	//If we have reached this point, first char was an open bracket, set this as the start of the buffer
	//and start parenCounter and index at 1
	StringBuilder retValBuffer = new StringBuilder("(");
	
	//represents (number of open brackets) - (number of closed brackets), starts at 1 because we add in the open bracket above
	int parenCounter = 1;
	
	//index starts at 1, as we've already checked first counter
	int i = 1;
	
	//While there are still unclosed brackets keep building out the string
	while (parenCounter > 0) {
		//get most recent character and append
		char c = programSubstring.charAt(i);
		retValBuffer.append(c);
		//if we encounter a closing decrement parenCounter and if we encounter a closing increment
		if (c == ')') {
			parenCounter--;
		} else if (c == '(') {
			parenCounter++;
		}
		
		
		i++;
	}
	
	return retValBuffer.toString();
}

/**
 * Finds the index of the next occurrence of an ite function in program.
 * @param program
 * @return If an ite is found, returns the index where the ite function begins i.e. the proceeding open bracket directly before ite.
 *  If no ite is found, returns -1.
 */
public static int findNextITEIndex(String program) {
	StringBuilder buffer = new StringBuilder("");
	
	//build out string until white space is encountered and then check if it is an ite
	for (int i = 0; i < program.length(); i++) {
		
		if (program.charAt(i) == ' ') {
			buffer.append(program.charAt(i));
			//if we have built an ite, return the starting index of this ite
			if (buffer.toString().equals("(ite ")) {
				return i-4;
			}
			
			//otherwise, reset the buffer to empty and keep searching
			buffer = new StringBuilder("");
		} else {
			//white space not encountered, so just add to string 
			buffer.append(program.charAt(i));
		}
		

	}
	
	//No ite was found, so return -1.
	return -1;
}

public static String scanToSpace(String str) {
	StringBuffer buf = new StringBuffer();
	
	for (int i = 0; i < str.length(); i++) {
		char c = str.charAt(i);
		if (c == ' ') {
			return buf.toString();
		} 
		
		buf.append(c);
	}
	
	return buf.toString();
}



public static void main(String[] args) throws Exception {
	
	String benchmarkFile = "src/main/resources/benchmarks/questionThree.sl";
//	String benchmarkFile = "src/main/resources/benchmarks/fg_max3.sl";
	//String benchmarkFile = "src/main/resources/benchmarks/distinctOne.sl";
	Benchmark benchmark = Benchmark.parseBenchmark(benchmarkFile);
	
	//System.out.println(Utils.transformToJustEqualsAndDistinctsMI(benchmark));
}

}
