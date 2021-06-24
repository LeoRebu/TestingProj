import static org.junit.Assert.*;
import java.util.Calendar;
import java.util.Date;

import org.junit.Test;

public class ReportTest {
	Report highSwarmRisk, medSwarmRisk, lowSwarmRisk, needsSuper1, needsSuper2, highStarveRisk, lowStarveRisk;
	Report bonus;
	
	public ReportTest() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		highSwarmRisk = new Report(cal.getTime(),10,5,11,true,true,0,0);
		medSwarmRisk = new Report(cal.getTime(),10,5,8,true,true,1,(float)0.5);
		lowSwarmRisk = new Report(cal.getTime(),9,3,10,true,false,0,0);
		needsSuper1 = new Report(cal.getTime(),7,5,8,true,true,1,(float)0.9); 
		needsSuper2 = new Report(cal.getTime(),9,4,10,true,false,0,0); 
		highStarveRisk = new Report(cal.getTime(),11,0,10,true,true,1,(float)0.9); 
		lowStarveRisk = new Report(cal.getTime(),9,4,10,true,false,0,0); 
	}
	
	@Test
	public void testConstructor() {
		assertNotNull(highSwarmRisk);
		assertNotNull(medSwarmRisk);
		assertNotNull(lowSwarmRisk);
		assertNull(bonus);
	}
	
	@Test
	public void testConstruction() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		Report testRep = new Report();
		int broodFrames = 8;
		
		testRep.setDate(cal.getTime());
		testRep.setBroodFrames(broodFrames);
		testRep.setHoneyFrames(2);
		testRep.setBeeFrames(10);
		testRep.setSeenQueen(false);
		testRep.setSwarmCells(true);
		testRep.setNumSupers(1);
		testRep.setPercTopSuper((float)0.9);
		
		assertEquals(2, testRep.getHoneyFrames());
		assertEquals(10, testRep.getBeeFrames());
		assertEquals(1, testRep.getNumSupers());	
		assertTrue(!testRep.getSeenQueen());	
		assertTrue(testRep.getSwarmCells());
	    assertSame(testRep.getBroodFrames(),broodFrames);
		assertTrue(testRep.getPercTopSuper() == (float)0.9);
		
	}



	@Test
	public void testSwarm() {
		assertTrue(highSwarmRisk.swarmRisk()==5);
		assertTrue(medSwarmRisk.swarmRisk()==3);
		assertTrue(lowSwarmRisk.swarmRisk()==0);
	}

	@Test
	public void testStarve() {
		assertEquals(5,highStarveRisk.starvingRisk());
		assertEquals(0,lowStarveRisk.starvingRisk());
	}
	
	@Test
	public void testSuper() {
		assertTrue(needsSuper1.needsSuper());
		assertTrue(needsSuper2.needsSuper());
		assertTrue(needsSuper2.needsSuper());
	}
	
	@Test
	public void testSuperPercentage() {
		highSwarmRisk.setPercTopSuper((float)0.5);
		if (highSwarmRisk.getNumSupers() == 0 && highSwarmRisk.getPercTopSuper() > 0)
			fail();
	}
	
	@Test
	public void testSwarmMCDC() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		
		Report reportMcdc = new Report(cal.getTime(),3,2,4,true,false,0,0);
		
		// Stato iniziale: tutto FALSE
		assertEquals(0, reportMcdc.swarmRisk());
		// 4 Possibili condizioni che possono incrementare il rischio di sciamatura
		// Condizione 1: favi di covata >9 (incrementa di 1)
		reportMcdc.setBroodFrames(10);
		assertEquals(1, reportMcdc.swarmRisk());
		// Condizione 2: presenza di celle di sciamatura (+ 2)
		reportMcdc.setSwarmCells(true);
		assertEquals(3, reportMcdc.swarmRisk());
		// Condizione 3: favi d'api >10 senza melari (+ 1)
		reportMcdc.setBeeFrames(11);
		assertEquals(4, reportMcdc.swarmRisk());
		
		// Condizione 4.1: favi di miele > 4 senza melari (+ 1)
		reportMcdc.setHoneyFrames(5);
		assertEquals(5, reportMcdc.swarmRisk());
		// Condizione 4.2: favi di miele > 4 con almeno un melario, riempimento <0.8) (- 2)
		reportMcdc.setNumSupers(1);
		assertEquals(3, reportMcdc.swarmRisk());
		// Condizione 4.3: favi di miele > 4 con almeno un melario, riempimento >=0.8) (+ 1)
		reportMcdc.setPercTopSuper((float)0.8);
		assertEquals(4, reportMcdc.swarmRisk());
	}
	
	@Test
	public void testStarveMcdc() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		Report reportMcdc = new Report(cal.getTime(),3,3,4,true,false,1,(float)0.8);
		assertEquals(0,reportMcdc.starvingRisk());
		// 5 Possibili condizioni che possono incrementare il rischio di denutrizione
		// Condizione 1: favi di miele < 2 (+ 1)
		reportMcdc.setHoneyFrames(1);
		assertEquals(1,reportMcdc.starvingRisk());
		// Condizione 2: fmiele<2 E numero di melari == 0 (+ 2)
		reportMcdc.setNumSupers(0);
		assertEquals(3,reportMcdc.starvingRisk());
		// Condizione 3.1: fmiele<2 E numero di melari > 0 (- 2) E favi d'api > 9 (+ 1)
		reportMcdc.setNumSupers(1);
		reportMcdc.setPercTopSuper((float)0.8);
		reportMcdc.setBeeFrames(10);
		assertEquals(2,reportMcdc.starvingRisk());
		// Condizione 3.2: fmiele<2 E numero di melari > 0 E favi di covata > 10 (+ 2)
		reportMcdc.setBroodFrames(11);
		assertEquals(4,reportMcdc.starvingRisk());
		// Condizione 5: favi di miele == 0 
		reportMcdc.setHoneyFrames(0);
		assertEquals(5,reportMcdc.starvingRisk());
	}
	
	@Test
	public void testStarveCtWedge() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		// Test 37 - none
		Report rep = new Report(cal.getTime(),10,4,9,true,false,0,0);
		assertTrue(rep.starvingRisk()<2);
		// Test 39 - emergency
		rep = new Report(cal.getTime(),11,0,11,true,false,2,(float)0.4);
		assertTrue(rep.starvingRisk()>3);
		// Test 41 - warning
		rep = new Report(cal.getTime(),11,1,1,true,false,0,0);
		assertTrue(rep.starvingRisk()>1 &&rep.starvingRisk()<4);
		// Test 43 - warning
		rep = new Report(cal.getTime(),5,1,9,true,false,0,0);
		assertTrue(rep.starvingRisk()>1 &&rep.starvingRisk()<4);
		// Test 45 - emergency
		rep = new Report(cal.getTime(),10,0,10,true,false,0,0);
		assertTrue(rep.starvingRisk()>3);
	}
	
	@Test
	public void testSuperNeedCtWedge() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		// Test 23
		Report rep = new Report(cal.getTime(),5,2,5,true,false,1,(float)0.8);
		assertTrue(!rep.needsSuper());
		// Test 24
		rep = new Report(cal.getTime(),5,4,4,true,false,1,(float)0.8);
		assertTrue(rep.needsSuper());
		// Test 25
		rep = new Report(cal.getTime(),5,6,4,true,false,2,(float)0.8);
		assertTrue(rep.needsSuper());
		// Test 26
		rep = new Report(cal.getTime(),5,0,4,true,false,2,(float)1);
		assertTrue(!rep.needsSuper());
		// Test 32
		rep = new Report(cal.getTime(),5,1,4,true,false,0,0);
		assertTrue(!rep.needsSuper());
	}
	
	@Test
	public void testSuperCoverage() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);

		Report rep = new Report(cal.getTime(),5,4,5,true,false,1,(float)0.7);
		assertTrue(!rep.needsSuper());
		rep.setNumSupers(3);
		assertTrue(!rep.needsSuper());
		rep.setBeeFrames(14);
		rep.setHoneyFrames(14);
		rep.setBroodFrames(14);
		rep.setNumSupers(4);
		rep.setDate(null);
		assertTrue(!rep.needsSuper());
	}
	

	@Test
	public void testConditionCoverage() {
		Calendar cal = Calendar.getInstance();
		cal.set(2020,0,1);
		// Test 23
		Report rep = new Report(cal.getTime(),-1,15,-1,true,false,5,(float)2);

		rep = new Report (cal.getTime(),13,-1,15,true,false,-1,-1); 
		Date d = rep.getDate();
		
		rep.setBeeFrames(-1);
		rep.setHoneyFrames(-1);
		rep.setBroodFrames(-1);
		rep.setNumSupers(-1);
		rep.setPercTopSuper(-1);
		rep.setPercTopSuper(2);

		assertTrue(rep.getBeeFrames() == 0);
		assertTrue(rep.getHoneyFrames() == 0);
		assertTrue(rep.getBroodFrames() == 0);
	}
}
