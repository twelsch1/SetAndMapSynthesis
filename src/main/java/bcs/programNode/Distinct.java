package bcs.programNode;

import bcs.datatypes.IntData;


public class Distinct extends Node {

	public String toString() {
		return "distinct";
	}
	
	public String getNodeType() { return "boolean";}
	

	public void eval(final IntData input, final int[] variables) {
		int left, right;

		children[0].eval(input, variables);
		left = input.x;
		children[1].eval(input, variables);
		right = input.x;
		if (left != right)
			input.x = 1;
		else
			input.x = 0;

	}
}
