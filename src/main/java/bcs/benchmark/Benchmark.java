package bcs.benchmark;

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Scanner;

import bcs.programNode.Node;
import bcs.utils.Utils;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class Benchmark {

	private String functionName;
	private String assertionString;
	private String funString;
	private String[] variableNames;
	private String[] synthesisVariableNames;
	private String[] definedFunctions;
	private String[] definedFunctionNames;
	private ArrayList<ArrayList<String>> variances;
	private String logic;

	public Benchmark(String functionName, String assertionString, String funString, String[] variableNames,
			String[] definedFunctions, String[] definedFunctionNames, String logic, ArrayList<ArrayList<String>> variances) {
		this.functionName = functionName;
		this.assertionString = assertionString;
		this.funString = funString;
		this.variableNames = variableNames;
		this.definedFunctions = definedFunctions;
		this.definedFunctionNames = definedFunctionNames;
		this.logic = logic;
		this.variances = variances;
	}

	public String getFunctionName() {
		return functionName;
	}

	public String getAssertionString() {
		return assertionString;
	}

	public String getFunString() {
		return funString;
	}

	public String[] getVariableNames() {
		return variableNames;
	}

	public String[] getDefinedFunctions() {
		return definedFunctions;
	}

	public String[] getDefinedFunctionNames() {
		return definedFunctionNames;
	}
	
	public String getLogic() {
		return logic;
	}
	
	public ArrayList<ArrayList<String>> getVariances() {
		return variances;
	}
	
	public String[] getSynthesisVariableNames() {
		return synthesisVariableNames;
	}

	public void setSynthesisVariableNames(String[] synthesisVariableNames) {
		this.synthesisVariableNames = synthesisVariableNames;
	}

	public static Benchmark parseBenchmark(String filename) throws Exception {
		File file = new File(filename);
		String fileContent = Files.readString(file.toPath());
		
		//removes any space between ( and characters such that "( func " becomes "(func "
		fileContent = fileContent.replaceAll("\\(\s+", "(");
		ArrayList<String> subStrings = new ArrayList<>();

		int parenCounter = 0;
		String subString = "";
		for (int i = 0; i < fileContent.length(); i++) {
			subString += fileContent.charAt(i);
			if (fileContent.charAt(i) == '(') {
				parenCounter++;
			} else if (fileContent.charAt(i) == ')') {
				parenCounter--;
			}

			if (parenCounter == 0 && !subString.isBlank()) {
				subStrings.add(subString.strip());
				subString = "";
			}
		}

		String functionName = "";
		String funString = "";
		String logic = "";
		ArrayList<String> variables = new ArrayList<>();
		ArrayList<String> definedFunctions = new ArrayList<>();
		ArrayList<String> definedFunctionNames = new ArrayList<>();
		ArrayList<String> constraints = new ArrayList<>();
		for (String s : subStrings) {
			if (s.contains("set-logic")) {
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // it's directly after synth-fun, just discard it
					logic = scan.next();
					int toStrip = logic.lastIndexOf(")");
					logic = logic.substring(0,toStrip);
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}
			}
			else if (s.contains("synth-fun")) {
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // it's directly after synth-fun, just discard it
					functionName = scan.next();
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}

				funString = s.replace("synth-fun", "define-fun");
				funString = funString.substring(0, funString.length() - 1) + " funToken;)";
			} else if (s.contains("declare-var")) {
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // it's directly after declare-var, for now we don't need to worry about the
									// type afterwards
					// though we will need to eventually
					variables.add(scan.next());
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}
			} else if (s.contains("define-fun")) {
				definedFunctions.add(s);
				try (Scanner scan = new Scanner(s)) {
					scan.next(); // function name directly after define-fun, for now we don't need to worry about
									// everything afterwards
					definedFunctionNames.add(scan.next());
				} catch (Exception e) {
					e.printStackTrace();
					throw e;
				}
			} else if (s.contains("constraint")) {
				// System.out.println(s);
				int idx = 12;
				constraints.add(s.substring(idx, s.length() - 1).trim());
			}
		}

		// System.out.println(functionName);
		// System.out.println(funString);
		String assertionString = "";
		if (constraints.size() == 1) {
			assertionString = constraints.get(0);
		} else {
			assertionString = "(and ";
			for (String con : constraints) {
				assertionString += con + " ";
			}
			assertionString += ")";
		}

		//System.out.println(assertionString);
		assertionString = Node.formatProgramStringForNode(assertionString);
		ArrayList<ArrayList<String>> variances = findVariances(assertionString,"("+ functionName + " ");
		
		//String[] tmpVars = {"tmpvar1;", "tmpvar2;"};
		//String prog = "(- tmpvar1; tmpvar2;)";
		
		//System.out.println(transformSIProgramToMI(prog, variances, tmpVars));
		if (variances == null) {
			throw new Exception("Unsupported Benchmark");
		}
		// System.out.println(assertionString);
		String[] definedFunctionsArr;
		String[] definedFunctionNamesArr;
		if (definedFunctions.isEmpty()) {
			definedFunctionsArr = null;
			definedFunctionNamesArr = null;
		} else {
			definedFunctionsArr = definedFunctions.toArray(new String[definedFunctions.size()]);
			definedFunctionNamesArr = definedFunctionNames.toArray(new String[definedFunctionNames.size()]);

		}
		Benchmark b = new Benchmark(functionName, assertionString, funString, variables.toArray(new String[variables.size()]),
				definedFunctionsArr, definedFunctionNamesArr,logic, variances);
		
		b.setSynthesisVariableNames(variables.toArray(new String[variables.size()]));
		
		return b;
	}
	
	private static ArrayList<ArrayList<String>> findVariances(String assertions, String targetFunction) {
		
		ArrayList<ArrayList<String>> variances = new ArrayList<>();
		HashSet<String> varianceStrings = new HashSet<>();
		String principalString = "";

		String sub = assertions;
		while (true) {
			
			//System.out.println(sub);
			int idx = sub.indexOf(targetFunction);
			
			if (idx == -1) {
				break;
			}
			
			String funStringToExtract = Utils.extractNextFunction(sub.substring(idx));
			//System.out.println("Extracting: " + funStringToExtract);
			varianceStrings.add(funStringToExtract);
			principalString = funStringToExtract;
			idx += funStringToExtract.length();
			sub = sub.substring(idx);
		}
		
		ArrayList<String> principals = extractParameters(principalString.substring(targetFunction.length()));
		
		
		for (String s : varianceStrings) {
			ArrayList<String> checkParams = new ArrayList<>();
			checkParams.addAll(principals);
			ArrayList<String> params = extractParameters(s.substring(targetFunction.length()));
			
			for (String param : params) {
				if (checkParams.contains(param)) {
					checkParams.remove(param);
				} else {
					return null;
				}
			}
			
			variances.add(params);
		}
		
		
		
		return variances;
	}
	
	private static ArrayList<String> extractParameters(String varianceWithoutLeadingFunction) {
		
		
		ArrayList<String> params = new ArrayList<>();
		String sub = varianceWithoutLeadingFunction;
		String orig = sub;
		//System.out.println(sub);
		int idx = 0;
		while (true) {
			String nextParam = Utils.extractNextFunction(sub);
			
			params.add(nextParam);
			idx += nextParam.length() + 1;
			
			if (idx >= orig.length()) {
				break;
			}
			
			sub = orig.substring(idx);
			
		}
		
		return params;
		
	}
	

}
