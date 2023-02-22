package bcs.programNode;

import bcs.datatypes.IntData;

public class Implies extends Node {

	public String toString() {
		return "=>";
	}

	public String getNodeType() { return "boolean";}

	public void eval(final IntData input, final int[] variables) {

		children[0].eval(input, variables);

		int lhs = input.x;
		children[1].eval(input, variables);
		if (lhs == 1 && input.x == 0) {
			input.x = 0;
		} else {
			input.x = 1;
		}
	}

}
