package sms.verification;

import java.util.ArrayList;

/**
 * A class that holds input/output examples, and contains utility functions for handling them. 
 * @author Thomas Welsch
 *
 */
public class CounterExample {
	/**
	 * Array that holds function inputs.
	 */
	private int[] inputs;
	/**
	 * The output corresponding to that input obtained through verification.
	 */
	private int output;
	
	
	
	public CounterExample(int[] inputs, int output) {
		this.inputs = inputs;
		this.output = output;
	}
	
	public int[] getInputs() {
		return inputs;
	}
	public void setInputs(int[] inputs) {
		this.inputs = inputs;
	}
	public int getOutput() {
		return output;
	}
	public void setOutput(int output) {
		this.output = output;
	}
	
	@Override
	/**
	 * Creates a String Mapping that is unique to each I/O configuration. Can be used to check for duplicates.
	 */
	public String toString() {
		String retVal = "Input: ";
		for(int i = 0; i < inputs.length; i++) {
			retVal += inputs[i] + "\n";
		}
		retVal += "Output: " + output;
		
		
		return retVal;
	}
	
	
	/**
	 * A helper function that converts an ArrayList of CounterExample objects to a 2D double array. Potentially useful
	 * for working with external libraries.
	 * @param counterExamples
	 * @return double[][] - 2D array of doubles representing the counter
	 */
	public static double[][] examplesToPoints(ArrayList<CounterExample> counterExamples) {
		
		int cols = counterExamples.get(0).getInputs().length;
		double[][] points = new double[counterExamples.size()][cols];
		
		for (int i = 0; i < counterExamples.size(); i++) {
			int[] exampleInputs = counterExamples.get(i).getInputs();
			
			for (int j = 0; j < cols; j++) {
				points[i][j] = exampleInputs[j];
			}
		}
		
		
		return points;
	}
	
	@Override
	public boolean equals(Object o) {
		CounterExample comp = (CounterExample) o;
		return this.toString().equals(comp.toString());
	}
	

}
