abstract sig User {}

abstract sig Report {
    about: one Internship,
}

sig Student extends User{
	studiesAt: one University,
    appliesFor: set Internship,
    particiaptesIn: set Internship,
    fills: set Form,
    writes: set Report,
}

sig Company extends User{
    creates: set Internship,
    archives: set PastProject,
    writes: set Report,
}

sig University extends User{
    supervises: set Student,
    reads: set Complaint,
}

sig Internship {}

sig PastProject {}

sig Complaint extends Report {}

sig Feedback extends Report {}

sig Form {
    _for_: one Internship,
}

// Facts
// All internships must have exactly one company that offers them
fact OneOfferingCompany {
    all i: Internship |
    one c: Company | i in c.creates
}

// All students must study at exactly one university and that university must supervise
// them.
fact EveryStudentBelongsToUniversity {
    all s: Student | 
    one u: University | (s.studiesAt = u) and (s in u.supervises)
}

// All univesities can only read complaints that are made for internships involving
// their students.
fact UniversityReadsRelevantComplaints {
    all u: University, c: Complaint |
    (c in u.reads) implies (c.about in u.supervises.particiaptesIn)
}

// Each student can only fill forms for internships that they have applied for.
fact StudentFillsFormsForAppliedInternships {
    all s: Student, f: Form |
    (f in s.fills) implies (f._for_ in s.appliesFor)
}

// Each student can submit only one form per internship.
fact UniqueFormPerStudentPerInternship {
    all s: Student, i: Internship |
    lone f: Form | (f in s.fills) and (f._for_ = i)
}

// Each form must be filled by a single student.
fact FormFilledBySingleStudent {
    all f: Form |
    one s: Student | f in s.fills
}

// Each student can only participate in internships for which they have applied for and
// filled a form.
fact StudentParticipatesInAppliedInternships {
    all s: Student, i: Internship |
    (i in s.particiaptesIn) implies ((i in s.appliesFor) and
    (one f: Form | f._for_ = i and f in s.fills))
}

// Each past project is associated with a company that has offered it.
fact PastProjectHasOfferingCompany {
    all p: PastProject |
    one c: Company | p in c.archives
}

// A report can only be written by a single student or a single company involved in the 
// internship and cannot have more than one author.
fact UniqueReportAuthor {
    all r: Report |
        (one s: Student | r in s.writes and no c: Company | r in c.writes) or
        (one c: Company | r in c.writes and no s: Student | r in s.writes)
}
// A report can only be written by a student participating in the internship.
fact ReportWrittenByParticipatingStudent {
    all r: Report, s: Student |
    (r in s.writes) implies (r.about in s.particiaptesIn)
}

// A company can only write reports for an internship it has created and in which at least one
// student participates.
fact ReportWrittenByOfferingCompany {
    all r: Report, c: Company |
    (r in c.writes) implies (r.about in c.creates and some s: Student | r.about in s.particiaptesIn)
}

// A complaint can only be made if there is another party involved in the internship.
fact ComplaintMadeForActiveInternship {
    all c: Complaint |
    some s: Student | c.about in s.particiaptesIn
}

// Each student or company can only write one feedback for each internship they are
// involved in.
fact UniqueFeedbackPerInternship {
    all s: Student, c: Company, i: Internship |
    lone f: Feedback | (f in s.writes or f in c.writes) and f.about = i
}

// ------------------ Tests ------------------

// Predicate showing a basic scenario where one company offers one internship and
// one student applies.
pred scenarioOneStudentOneInternship {
    one c: Company, s: Student, i: Internship |
        c.creates = i and s.appliesFor = i
}
run scenarioOneStudentOneInternship for 5 but exactly 2 Student

// Predicate showing a basic scenario where one company offers one internship and
// two students apply for it.
pred scenarioTwoStudentsOneInternship {
    one c: Company, i: Internship | some s1, s2: Student |
        c.creates = i and s1.appliesFor = i and s2.appliesFor = i
        and s1 != s2
}
run scenarioTwoStudentsOneInternship for 5 but exactly 2 Student

// ------------------------------------------------------------------------------------------


// Test complete internship lifecycle with form submission and participation
pred scenarioCompleteInternshipProcess {
    // There exists a company, student, university, and internship
    some c: Company, s: Student, u: University, i: Internship, f: Form |
        // Company creates internship
        i in c.creates and
        // Student studies at university
        s.studiesAt = u and
        // Student applies for internship
        i in s.appliesFor and
        // Student fills form for internship
        f in s.fills and
        f._for_ = i and
        // Student participates in internship
        i in s.particiaptesIn
}
run scenarioCompleteInternshipProcess for 5

// Test complaint submission scenario
pred scenarioComplaintSubmission {
    some c: Company, s: Student, u: University, i: Internship, comp: Complaint |
        // Basic setup
        i in c.creates and
        s.studiesAt = u and
        i in s.particiaptesIn and
        // Complaint is written by student about their internship
        comp in s.writes and
        comp.about = i and
        // University reads the complaint
        comp in u.reads
}
run scenarioComplaintSubmission for 5

// Test feedback submission from both parties
pred scenarioFeedbackSubmission {
    some c: Company, s: Student, i: Internship, f1, f2: Feedback |
        // Basic setup
        i in c.creates and
        i in s.particiaptesIn and
        // Both student and company write feedback
        f1 in s.writes and
        f2 in c.writes and
        f1.about = i and
        f2.about = i and
        f1 != f2
}
run scenarioFeedbackSubmission for 5

// Test multiple students applying for same internship with form submission
pred scenarioMultipleStudentApplications {
    some c: Company, i: Internship, f1, f2: Form |
        some disj s1, s2: Student |
            // Company creates internship
            i in c.creates and
            // Both students apply
            i in s1.appliesFor and
            i in s2.appliesFor and
            // Both students fill forms
            f1 in s1.fills and
            f2 in s2.fills and
            f1._for_ = i and
            f2._for_ = i and
            // Only one student participates
            i in s1.particiaptesIn and
            i not in s2.particiaptesIn
}
run scenarioMultipleStudentApplications for 6

// Test past project archival
pred scenarioPastProjectArchival {
    some c: Company, p: PastProject, i: Internship |
        // Company creates internship and archives past project
        i in c.creates and
        p in c.archives and
        // Some student must have participated
        some s: Student |
            i in s.particiaptesIn
}
run scenarioPastProjectArchival for 5

// Test multiple universities supervising different students
pred scenarioMultipleUniversities {
    some disj u1, u2: University, s1, s2: Student, c: Company, i: Internship |
        // Students at different universities
        s1.studiesAt = u1 and
        s2.studiesAt = u2 and
        // Both apply for same internship
        i in c.creates and
        i in s1.appliesFor and
        i in s2.appliesFor
}
run scenarioMultipleUniversities for 6

// Negative test: student cannot participate without applying
pred assertNoParticipationWithoutApplication {
    some s: Student, i: Internship |
        i in s.particiaptesIn and
        i not in s.appliesFor
}
run assertNoParticipationWithoutApplication for 5 expect 0

// Negative test: student cannot fill form without applying
pred assertNoFormWithoutApplication {
    some s: Student, f: Form |
        f in s.fills and
        f._for_ not in s.appliesFor
}
run assertNoFormWithoutApplication for 5 expect 0