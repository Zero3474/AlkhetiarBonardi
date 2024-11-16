abstract sig User {}

abstract sig Report {
    about: one Internship,
}

sig Student extends User {
	studiesAt: one University,
    appliesFor: set Internship,
    particiaptesIn: set Internship,
    fills: set Form,
    writes: set Report,
}

sig Company extends User {
    creates: set Internship,
    archives: set PastProject,
    writes: set Report,
}

sig University extends User {
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

// All students must study at exactly one university and that university
// must supervise them
fact EveryStudentBelongsToUniversity {
    all s: Student | 
    one u: University | (s.studiesAt = u) and (s in u.supervises)
}

// All univesities can only read complaints that are made for internships
// involving    their students
fact UniversityReadsRelevantComplaints {
    all u: University, c: Complaint |
    (c in u.reads) implies (c.about in u.supervises.particiaptesIn)
}

// Each student can only fill forms for internships that they have applied
// for
fact StudentFillsFormsForAppliedInternships {
    all s: Student, f: Form |
    (f in s.fills) implies (f._for_ in s.appliesFor)
}

// Each student can submit only one form per internship
fact UniqueFormPerStudentPerInternship {
    all s: Student, i: Internship |
    lone f: Form | (f in s.fills) and (f._for_ = i)
}

// Each form must be filled by a single student
fact FormFilledBySingleStudent {
    all f: Form |
    one s: Student | f in s.fills
}

// Each student can only participate in internships for which they have
// applied for and filled a form
fact StudentParticipatesInAppliedInternships {
    all s: Student, i: Internship |
    (i in s.particiaptesIn) implies ((i in s.appliesFor) and
    (one f: Form | f._for_ = i and f in s.fills))
}

// Each past project is associated with a company that has offered it
fact PastProjectHasOfferingCompany {
    all p: PastProject |
    one c: Company | p in c.archives
}

// A report can only be written by a single student or a single company
// involved in the internship and cannot have more than one author
fact UniqueReportAuthor {
    all r: Report |
        (one s: Student | r in s.writes and no c: Company | r in c.writes) or
        (one c: Company | r in c.writes and no s: Student | r in s.writes)
}
// A report can only be written by a student participating in the internship
fact ReportWrittenByParticipatingStudent {
    all r: Report, s: Student |
    (r in s.writes) implies (r.about in s.particiaptesIn)
}

// A company can only write reports for an internship it has created and
// in which at least one student participates
fact ReportWrittenByOfferingCompany {
    all r: Report, c: Company |
    (r in c.writes) implies (r.about in c.creates and 
    some s: Student | r.about in s.particiaptesIn)
}

// A complaint can only be made if there is another party involved in the
// internship
fact ComplaintMadeForActiveInternship {
    all c: Complaint |
    some s: Student | c.about in s.particiaptesIn
}

// Each student or company can only write one feedback for each internship
// they are involved in
fact UniqueFeedbackPerInternship {
    all s: Student, c: Company, i: Internship |
    lone f: Feedback | (f in s.writes or f in c.writes) and f.about = i
}

// ------------------ Scenarios ------------------

// Predicate showing a basic scenario where one company offers an internship
// and one student applies for it.
pred scenarioOneCompanyOneStudent {
    one c: Company, i: Internship, s: Student |
        c.creates = i and s.appliesFor = i and not i in s.particiaptesIn
}
run scenarioOneCompanyOneStudent for 3 but exactly 1 Company, 1 Internship,
1 Student

// Predicate showing a basic scenario where one company offers an internship 
// and two students apply for it.
pred scenarioTwoStudentsCompeting {
    one c: Company, i: Internship | 
    some s1, s2: Student |
        c.creates = i and s1.appliesFor = i and s2.appliesFor = i
        and s1 != s2
}
run scenarioTwoStudentsCompeting for 5 but exactly 1 Company, 1 Internship,
2 Student

// Predicate showing a comprehensive scenario where there are multiple
// companies offering internships and multiple students applying for them
pred scenarioMultipleCompaniesMultipleStudents {
    # Company > 2
    # Internship > 2
    # University > 3
    # PastProject < 3
    # Complaint < 4
    one s: Student | #s.appliesFor = 0
    all i: Internship | #i.~appliesFor < 3 and #i.~particiaptesIn < 3
}
run scenarioMultipleCompaniesMultipleStudents for 15 but exactly 7 Student