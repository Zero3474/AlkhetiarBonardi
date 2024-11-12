enum InternshipState {Open, FirstScreening,  SecondScreening, Ranking, Ongoing, Finished}
enum Status {Pending, Accepted, Rejected}

sig Student {
	university: one University
}

sig Company {
    description: one String,
    previousProjects: set String,
    internships: set Internship
}

sig University {
    managesComplaints: set String
}

sig Internship {
    state: one InternshipState,
    title: one String,
    skills: set String,
    experienceRequired: set String,
    deadline: one String,
    location: one String
}

sig Application {
    applicant: one Student,
    position: one Internship,
    status: one Status
}

pred show {}

run show for 3 but 1 Internship
