select RunId, SessionId, Letter, SubmitTime, Accepted
from Sessions natural join Runs
where TeamId = :TeamId and ContestId = :ContestId