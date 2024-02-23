package sms.optional;

import java.util.ArrayList;

import sms.verification.CounterExample;

/**
 * 
 * An optional implementation of a class that maintains a list of CounterExamples. This list is
 * appended using <strong>appendToCounterExample(CounterExample ce)</strong> and retrieved using 
 * <strong>retrieveActiveCounterExamples()</strong>. 
 * <br><br>
 
 * Internally, the list is actually two lists for synthesis of predicates i.e.
 * one list for positive CounterExamples and one for negative. The cap on these lists is calculated as maxTests/2 
 * and maintained separately for each such that the examples will tend toward being balanced.
 * @author Thomas Welsch
 *
 */
public class CounterExamplesManager {

	/**
	 * List of active CounterExamples for program synthesis.
	 */
	private ArrayList<CounterExample> counterExamples = new ArrayList<>();
	
	/**
	 * List of active positive CounterExamples for predicate synthesis.
	 */
	private ArrayList<CounterExample> positiveCounterExamples = new ArrayList<>();
	
	/**
	 * List of active negative CounterExamples for predicate synthesis.
	 */
	private ArrayList<CounterExample> negativeCounterExamples = new ArrayList<>();
	
	/**
	 * List of all discarded CounterExamples.
	 */
	private ArrayList<CounterExample> discardedCounterExamples = new ArrayList<>();

	
	private String synthesisType;
	private boolean allowDuplicates;
	private int maxTests;
	
	/**
	 * Standard constructor that sets internal class values based off parameters.
	 * @param allowDuplicates Determines whether there can be duplicates among active CounterExamples.
	 * @param maxTests Cap on the number of active CounterExamples allowed.
	 * @param synthesisType The synthesis type, there are two options, "predicate" and "program", if another string is given defaults to the latter
	 */
    public CounterExamplesManager(boolean allowDuplicates, int maxTests, String synthesisType) {
		this.allowDuplicates = allowDuplicates;
		this.maxTests = maxTests;
		this.synthesisType = synthesisType;
	}

	/**
     * Attempts to add CounterExample ce to the list of CounterExamples being tracked. 
     * If duplicates are not allowed and the counterexample is contained in list already, ce is not added.
     * Otherwise, ce is appended to the list. If the list size is over maxTests, the oldest test from the list is discarded.
     * @param ce An I/O CounterExample.
     * @return true if ce is appended, false otherwise.
    */
    public boolean appendToCounterExamples(CounterExample ce) {
    	if (synthesisType.equals("predicate")) {
    		return predicateAppendToCounterExamples(ce);
    	} else {
    		return programAppendToCounterExamples(ce);
    	}
    }


    /**
     * Internal function that attempts to append to active counterExamples. Works as described in <strong> appendToCounterExample(CounterExample ce) </strong>.
     * @param ce An I/O CounterExample.
     * @return true if ce is appended, false otherwise.
     */
    private boolean programAppendToCounterExamples(CounterExample ce) {
    	//if already in active examples and no duplicates allowed, return false
    	if (counterExamples.contains(ce) && !allowDuplicates) {
    		return false;
    	}
    		
    	//add the example
    	counterExamples.add(ce);
    	
    	//if we are now over maxTests, remove the oldest test from the list and add to discard pile
    	if (counterExamples.size() > maxTests) {
    		discardedCounterExamples.add(counterExamples.remove(0));
    	}
    	
    	return true;
    }
    
    /**
     * Internal function that attempts to append to active counterExamples. Works similarly to as described in <strong> appendToCounterExample(CounterExample ce) </strong>.
     * The key difference is there are in fact two lists, negative and positive, so we first determine to which list ce should attempt to be added.
     * @param ce An I/O CounterExample.
     * @return true if ce is appended, false otherwise.
     */
    private boolean predicateAppendToCounterExamples(CounterExample ce) {
    	
    	//determine which list we should attempt to append
    	boolean positive = ce.getOutput() == 1;
    	
    	if (positive) {
    		//if example contained and no duplciates, return false
    		if (positiveCounterExamples.contains(ce) && !allowDuplicates) {
    			return false;
    		}
    		
    		//add to list
    		positiveCounterExamples.add(ce);
    		
    		//if over the cap, dictated by maxTests/2, remove oldest example and add to discard pile
    		if (positiveCounterExamples.size() > maxTests/2) {
    			discardedCounterExamples.add(positiveCounterExamples.remove(0));
    		}
    	} else {
    		//As above so below
    		
    		if (negativeCounterExamples.contains(ce) && !allowDuplicates) {
    			return false;
    		}
    		
    		negativeCounterExamples.add(ce);
    		
    		if (negativeCounterExamples.size() > maxTests/2) {
    			discardedCounterExamples.add(negativeCounterExamples.remove(0));
    		}
    	}
    	
    	return true;
    }
    
    
    
    /**
     * Retrieves the list of active CounterExamples.
     * @return The list of CounterExamples found that haven't been discarded (i.e. due to going over cap). 
     */
	public ArrayList<CounterExample> retrieveActiveCounterExamples() {
		if (synthesisType.equals("predicate")) {
			//concatenates positive and negative active CounterExamples into a single list
			ArrayList<CounterExample> predicateCounterExamples = new ArrayList<>();
			predicateCounterExamples.addAll(positiveCounterExamples);
			predicateCounterExamples.addAll(negativeCounterExamples);
			return predicateCounterExamples;
		} else {

			return counterExamples;
		}

	}
	
	/**
	 * Retrieves the list of any CounterExample found since construction. This includes examples that were discarded after maxTests cap was exceeded.
	 * @return The list of all CounterExamples found since construction.
	 */
	public ArrayList<CounterExample> retrieveActiveAndDiscardedCounterExamples() {
		//returns concatenation of active CounterExamples with discarded ones.
		ArrayList<CounterExample> retVal = new ArrayList<>();
		retVal.addAll(discardedCounterExamples);
		retVal.addAll(retrieveActiveCounterExamples());
		return retVal;
	}
	
	/**
	 * Counts the number of active positive CounterExamples.
	 * @return The number of active positive CounterExamples.
	 */
	public int countPositives() {
		return positiveCounterExamples.size();
	}
	
	/**
	 * Counts the number of active negative CounterExamples.
	 * @return The number of active negative CounterExamples.
	 */
	public int countNegatives() {
		return negativeCounterExamples.size();
	}
	
	/**
	 * Counts the number of active CounterExamples.
	 * @return The number of active CounterExamples.
	 */
	public int countCounterExamples() {
		if (synthesisType.equals("predicate")) {
			return positiveCounterExamples.size() + negativeCounterExamples.size();
		} else {
			return counterExamples.size();
		}
	}

    
    
    
    
    
    
}
