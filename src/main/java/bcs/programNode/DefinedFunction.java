package bcs.programNode;

import bcs.datatypes.IntData;

public class DefinedFunction extends Node {
	
	private String functionName;
	private String type;
	
	public String toString() { return functionName; }
	
	public String getNodeType() { return type;}
	
	public DefinedFunction(String functionName, String type) {
		this.functionName = functionName;
		this.type = type;
	}

	public void eval(final IntData input, final int[] variables) {
	    //Doesn't alter input, we just use this function for program extraction.
    }
	
	
	
	
}

