package sms.synthesizer;

/**
 * 
 * @author Thomas Welsch
 *
 */
public class SynthesisParameters {
	
	//These are the default values, only constructor is the default one
	
	private double pctOfPositives = 0.8;
	private long timeout = 60;
	private int maxThreads = 1;
	private int maxTermExpansions = 50;
	private int additionalTermsCap = 150;
	private int additionalTermsPerExtraction = 10;
	private int maxAdditionalTermLength = 30;
	private boolean extractAdditionalTerms = true;
	private boolean verifySuccess = true;
	private boolean skipToRepair = false;
	private boolean emulateCEGIS = false;
	private boolean emulateSTUN = false;
	private String branchwiseMode = "RBPS";

	
	public double getPctOfPositives() {
		return pctOfPositives;
	}

	public void setPctOfPositives(double pctOfPositives) {
		this.pctOfPositives = pctOfPositives;
	}

	public long getTimeout() {
		return timeout;
	}

	public void setTimeout(long timeout) {
		this.timeout = timeout;
	}

	public int getMaxTermExpansions() {
		return maxTermExpansions;
	}

	public void setMaxTermExpansions(int maxTermExpansions) {
		this.maxTermExpansions = maxTermExpansions;
	}

	public boolean isSkipToRepair() {
		return skipToRepair;
	}

	public void setSkipToRepair(boolean skipToRepair) {
		this.skipToRepair = skipToRepair;
	}

	public boolean isEmulateCEGIS() {
		return emulateCEGIS;
	}

	public void setEmulateCEGIS(boolean emulateCEGIS) {
		this.emulateCEGIS = emulateCEGIS;
	}

	public boolean isEmulateSTUN() {
		return emulateSTUN;
	}

	public void setEmulateSTUN(boolean emulateSTUN) {
		this.emulateSTUN = emulateSTUN;
	}

	public boolean isExtractAdditionalTerms() {
		return extractAdditionalTerms;
	}

	public void setExtractAdditionalTerms(boolean extractAdditionalTerms) {
		this.extractAdditionalTerms = extractAdditionalTerms;
	}

	public int getMaxThreads() {
		return maxThreads;
	}

	public void setMaxThreads(int maxThreads) {
		this.maxThreads = maxThreads;
	}

	public int getAdditionalTermsCap() {
		return additionalTermsCap;
	}

	public void setAdditionalTermsCap(int additionalTermsCap) {
		this.additionalTermsCap = additionalTermsCap;
	}

	public int getAdditionalTermsPerExtraction() {
		return additionalTermsPerExtraction;
	}

	public void setAdditionalTermsPerExtraction(int additionalTermsPerExtraction) {
		this.additionalTermsPerExtraction = additionalTermsPerExtraction;
	}

	public int getMaxAdditionalTermLength() {
		return maxAdditionalTermLength;
	}

	public void setMaxAdditionalTermLength(int maxAdditionalTermLength) {
		this.maxAdditionalTermLength = maxAdditionalTermLength;
	}

	public boolean isVerifySuccess() {
		return verifySuccess;
	}

	public void setVerifySuccess(boolean verifySuccess) {
		this.verifySuccess = verifySuccess;
	}

	public String getBranchwiseMode() {
		return branchwiseMode;
	}

	public void setBranchwiseMode(String branchwiseMode) {
		this.branchwiseMode = branchwiseMode;
	}
	
	
	
	
	
	
	
	
	
	
	
	

}
