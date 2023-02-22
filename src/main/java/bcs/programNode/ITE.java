package bcs.programNode;

import bcs.datatypes.IntData;

public class ITE extends Node {

	public String toString() {
		return "ite";
	}
	
	public String getNodeType() { return "int";}

	public void eval(final IntData input, final int[] variables) {

		children[0].eval(input, variables);

		if (input.x == 1) {
			children[1].eval(input, variables);
		} else {
			children[2].eval(input, variables);
		}

	}

}
