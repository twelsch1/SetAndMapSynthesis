package sms.programNode;

import sms.datatypes.IntData;

public class Mul extends Node {
	
	public String toString() { return "*"; }
	
	public String getNodeType() { return "int";}
	

	public void eval(final IntData input, final int[] variables) {
	    int result;
	
	    children[0].eval(input, variables);
	    result = input.x;
	
	    children[1].eval(input, variables);
	    input.x = result * input.x;
    }
}
