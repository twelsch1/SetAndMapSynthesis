# Set-And-Map-Synthesis
This is a library that implements the SetAndMapSynthesis Program Synthesis framework described in my thesis. 

In order to use it, import the project into Eclipse. Then take the ecj-27.jar file in src/main/resources and add it as an external
jar to the project's buildpath.

The two most significant implementations of SMS, LearningSMS and DeterministicSMS, can be run directly on a benchmark by running as java applications respectively the sms.learningSMS/LearningSMS.java and sms.deterministicSMS/DeterministicSMS.java classes.