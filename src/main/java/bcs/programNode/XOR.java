package bcs.programNode;

import bcs.datatypes.IntData;

public class XOR extends Node {

	public String toString() {
		return "xor";
	}

	public String getNodeType() { return "boolean";}

	public void eval(final IntData input, final int[] variables) {
		
		//adds one for each that is true
		int check = 0;
		for (int i = 0; i < children.length; i++) {
			children[i].eval(input, variables);
			check += input.x;
		}
		
		//if exactly one was true set input to 1 for true, otherwise 0 for false
		if (check == 1) {
			input.x = 1; 
		} else {
			input.x = 0;
		}
	}

}
