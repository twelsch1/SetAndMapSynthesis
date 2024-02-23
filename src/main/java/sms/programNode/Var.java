package sms.programNode;

import sms.datatypes.IntData;

public class Var extends Node {

	private String variableName;
	private int index;
	
	public String toString() { return variableName; }
    
    //Should change this so that it isn't hardcoded (i.e. support int, boolean, string etc.)
    //would need to update constructor and add class variable. Unnecessary for CLIA benchmarks, though.
    public String getNodeType() { return "int";}
    
    public Var(String variableName, int index) {
    	this.variableName = variableName;
    	this.index = index;
    }
	
	public void eval(final IntData input, final int[] variables) {
    	input.x = variables[index];
    }
}
