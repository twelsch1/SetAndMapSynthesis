package sms.programNode;

import sms.datatypes.IntData;

public class And extends Node {

	public String toString() {
		return "and";
	}
	
	public String getNodeType() { return "boolean";}

	public void eval(final IntData input, final int[] variables) {

		for (int i = 0; i < children.length; i++) {
			children[i].eval(input, variables);
			
			if (input.x == 0) {
				break;
			}
		}
		
	}
	
	

}
