package sms.programNode;

import sms.datatypes.IntData;

public class EphemeralBoolean extends Node {

	private int value;
	IntData rd = new IntData();

	public String toString() {
		return value == 1 ? "true" : "false";
	}

	public EphemeralBoolean(int value) {
		this.value = value;
	}
	
	public String getNodeType() { return "boolean";}

	@Override
	public void eval(final IntData input, final int[] variables) {
		input.x = value;
	}

}

