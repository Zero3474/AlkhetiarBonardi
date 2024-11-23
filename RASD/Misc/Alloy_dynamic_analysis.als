abstract sig User {}

var abstract sig Report {
    var about: one Internship,
}

sig Student extends User {
	studiesAt: one University,
    var appliesFor: set Internship,
    var participatesIn: set Internship,
    var fills: set Form,
    var writes: set Report,
}

sig Company extends User {
    var creates: set Internship,
    var archives: set Internship,
    var writes: set Report,
}

sig University extends User {
    var supervises: set Student,
    var reads: set Complaint,
}

sig Internship {
    var status: Status
}

var sig Complaint extends Report {}

var sig Feedback extends Report {}

var sig Form {
    var _for_: Internship,
}

enum Status { Open, Screening, Ongoing, Finished, PastProject }

// Facts
// ----------------------------------------------------------------------
// Old facts
// ----------------------------------------------------------------------

// All internships must have exactly one company that offers them or
// has archived them
fact OneOfferingCompany {
    always all i: Internship |
    one c: Company | i in c.creates or i in c.archives
}

// All students must study at exactly one university and that university
// must supervise them
fact EveryStudentBelongsToUniversity {
    always all s: Student | 
    one u: University | (s.studiesAt = u) and (s in u.supervises)
}

// All univesities can only read complaints that are made for internships
// involving their students
fact UniversityReadsRelevantComplaints {
    always all u: University, c: Complaint, i: Internship |
    c.about = i and c in u.reads implies
    once i in u.supervises.participatesIn
}

// Each student can only fill forms for internships that they have applied
// for
fact StudentFillsFormsForAppliedInternships {
    always all s: Student, f: Form |
    f in s.fills implies once f._for_ in s.appliesFor
}

// Each student can submit only one form per internship
fact UniqueFormPerStudentPerInternship {
    always all s: Student, i: Internship |
    lone f: Form | (f in s.fills) and (f._for_ = i)
}

// Each form must be filled by a single student
fact FormFilledBySingleStudent {
    always all f: Form |
    one s: Student | f in s.fills
}

// Each student can only participate in internships for which they have
// applied for and filled a form
fact StudentParticipatesInAppliedInternships {
    always all s: Student, i: Internship |
    i in s.participatesIn implies ((once i in s.appliesFor) and
    (once one f: Form | f._for_ = i and f in s.fills))
}

// A report can only be written by a single student or a single company
// cannot have more than one author
fact UniqueReportAuthor {
    always all r: Report |
    (one s: Student | r in s.writes and no c: Company | r in c.writes) or
    (one c: Company | r in c.writes and no s: Student | r in s.writes)
}

// A report can only be written by a student who is participating/has participated 
// in the internship
fact ReportWrittenByParticipatingStudent {
    always all s: Student, r: s.writes, i: Internship |
    (r.about = i and r in s.writes) implies once i in s.participatesIn
}

// A company can only write reports for an internship it has created and
// in which at least one student participates
fact ReportWrittenByOfferingCompany {
    always all r: Report, c: Company, i: Internship |
    (r.about = i and r in c.writes) implies (r.about in c.creates and
    some s: Student | once r.about in s.participatesIn)
}

// Each student or company can only write one feedback for each internship
// they are involved in
fact UniqueFeedbackPerInternship {
    always all s: Student, c: Company, i: Internship |
    lone f: Feedback | (f in s.writes or f in c.writes) and f.about = i
}

// ----------------------------------------------------------------------
// New facts
// ----------------------------------------------------------------------

// A student can only apply for internships that are open
fact StudentAppliesForOpenInternships {
    always all s: Student, i: Internship |
    i in s.appliesFor implies i.status = Open
}

// A student can only fill forms for internships during the screening phase
fact StudentFillsFormsDuringScreening {
    always all s: Student, f: Form |
    f in s.fills implies f._for_.status = Screening
}

// A student can only participate in internships that are ongoing
fact StudentParticipatesInOngoingInternships {
    always all s: Student, i: Internship |
    i in s.participatesIn implies i.status = Ongoing
}

// A complaint can only be made for internships that are ongoing
fact ComplaintMadeForOngoingInternship {
    always all c: Complaint |
    c.about.status = Ongoing
}

// A feedback can only be written for internships that are finished
fact FeedbackWrittenForFinishedInternship {
    always all f: Feedback |
    f.about.status = Finished
}

// A company can only remove an internship that is finished
fact CompanyCannotRemoveOngoingInternship {
    always all c: Company, i: Internship |
    i in c.creates and i.status != Finished implies i in c.creates'
}

// All internships will eventually be finished
fact AllInternshipsFinish {
    eventually all i: Internship |
    i.status = Finished
}

// All finished internships will eventually be archived by
// the company that created them
fact ArchiveFinishedInternships {
    always all c: Company, i: c.creates |
    i.status = Finished implies after (i.status = PastProject 
    and i in c.archives)
}

// A company can only archive an internship that is a past project
fact CompanyArchivesPastProject {
    always all c: Company, i: c.archives |
    i.status = PastProject
}

// The order of the statuses of an internship must be preserved
fact StatusOrder {
    always all i: Internship |
    (i.status = Open implies i.status' = Screening or i.status' = Open)
    and (i.status = Open implies eventually i.status = Screening)
    and (i.status = Screening implies i.status' = Ongoing)
    and (i.status = Ongoing implies i.status' = Finished)
    and (i.status = Finished implies i.status' = PastProject)
    and (i.status = PastProject implies i.status' = PastProject)
}

// Predicates -------------------------------------------------------------
pred InitialSituation {
    # Student = 3
    # Company = 2
    # University = 2
    # Internship = 3
    all i: Internship |
    i.status = Open
}

pred InternshipApplication {
    always all s: Student, i: Internship |
    i.status = Open implies i in s.appliesFor
}

pred InternshipExecution {
    always all i: Internship |
    (i.status = Ongoing implies some s: Student | i in s.participatesIn) and
    (i.status = Ongoing implies some cl: Complaint | cl.about = i) and
    (i.status = Ongoing implies some cl: Complaint, u: University | cl in u.reads) and
    (i.status = Finished implies some f: Feedback | f.about = i) and
    (i.status = Finished implies some c: Company, s: Student | # c.writes > 0 and # s.writes > 0)
}

pred show {
    InitialSituation;InternshipApplication;
    InternshipExecution
}
run show for 7