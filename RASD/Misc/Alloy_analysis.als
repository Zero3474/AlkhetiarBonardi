abstract sig User {}

abstract sig Report {
    about: one Internship,
}

sig Student extends User{
	studiesAt: one University,
    appliesTo: set Internship,
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
fact UniversityReadsComplaints {
    all u: University, c: Complaint |
    (c in u.reads) implies (c.about in u.supervises.particiaptesIn)
}

// Each student can submit only one form per internship.
fact UniqueFormPerStudentPerInternship {
    all s: Student, i: Internship |
        lone f: Form | (f in s.fills) and (f._for_ = i)
}

// Each student can only fill forms for internships that they have applied for.
fact StudentFillsFormsForAppliedInternships {
    all s: Student, f: Form |
    (f in s.fills) implies (f._for_ in s.appliesTo)
}

// Each student can only participate in internships that they have applied for and
// filled a form.
fact StudentParticipatesInAppliedInternships {
    all s: Student, i: Internship |
    (i in s.particiaptesIn) implies (i in s.appliesTo) and
    (one f: Form | f._for_ = i and f in s.fills)
}

// Each past project is associated with a company that has offered it.
fact PastProjectHasOfferingCompany {
    all p: PastProject |
    one c: Company | p in c.archives
}

// A report can only be written by one student or one company.
fact ReportWrittenByStudentOrCompany {
    all r: Report |
    (one s: Student | r in s.writes) or (one c: Company | r in c.writes)
}

// A complaint can only be made if there is another party involved in the internship.
fact ComplaintMadeForActiveInternship {
    all c: Complaint |
    some s: Student | c.about in s.particiaptesIn
}

// Each student or company can only write one feedback for each internship they are
// involved in.
fact UniqueFeedbackPerInternship {
    all r: Feedback |
    (one s: Student | r in s.writes and r.about in s.particiaptesIn) or 
    (one c: Company | r in c.writes and r.about in c.creates and 
    one s1: Student | s1.particiaptesIn = r.about)
}

// Predicate showing a basic scenario where one company offers one internship and
// one student applies.
pred scenarioOneStudentOneInternship {
    one c: Company, s: Student, i: Internship |
        c.creates = i and s.appliesTo = i
}
run scenarioOneStudentOneInternship for 5 but exactly 1 Student

// TODO: To be fixed
// Predicate showing a scenario where multiple students apply to the same internship.
pred scenarioMultipleStudentsApply {
    one c: Company, s1, s2: Student, i: Internship |
        i in c.creates and s1 != s2 and
        i in s1.appliesTo and i in s2.appliesTo
}
run scenarioMultipleStudentsApply for 10 but exactly 2 Student