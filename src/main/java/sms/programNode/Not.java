package sms.programNode;

import sms.datatypes.IntData;

public class Not extends Node {

	public String toString() {
		return "not";
	}

	public String getNodeType() { return "boolean";}

	public void eval(final IntData input, final int[] variables) {

		children[0].eval(input, variables);

		if (input.x == 1) {
			input.x = 0;
		} else {
			input.x = 1;
		}
	}

}
