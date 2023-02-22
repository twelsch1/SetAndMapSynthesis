package bcs.programNode;

import bcs.datatypes.IntData;

public class Or extends Node {

	public String toString() {
		return "or";
	}

	public String getNodeType() { return "boolean";}

	public void eval(final IntData input, final int[] variables) {
		
		for (int i = 0; i < children.length; i++) {
			children[i].eval(input, variables);
			
			if (input.x == 1) {
				break;
			}
		}
	}

}
