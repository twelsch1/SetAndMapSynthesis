package bcs.optional;

import bcs.utils.Utils;

/**
 * An optional class containing implementations of splitting algorithms.
 * @author Thomas Welsch
 *
 */
public class Splitter {

	
	/**
	 * Searches through program for ite functions. Returns the predicate of first ite function that is found and isn't just "true" or "false".
	 * @param program The program to be checked.
	 * @return Predicate from first ite that wasn't true or false, if none exist then just returns "true".
	 */
	public static String simpleSplit(String program) {
		
		String prog = program;
		while(true) {
			
			//find the next ite function
			int idx = Utils.findNextITEIndex(prog);
			
			//There were no more ite functions, just return "true"
			if (idx == -1) {
				return "true";
			}
			
			//extract the parts from the ite
			String[] parts = Utils.extractNextITEParts(prog, idx);
			//check that the predicate is not just "true" or "false", if is isn't then return the predicate
			if (!(parts[0].equals("true") || (parts[0].equals("false")))) {
				return parts[0];
			}
			
			//substring prog such that we delete the most recent occurence of "(ite "
			prog = prog.substring(idx+5);
			
	}
		
	}

}
